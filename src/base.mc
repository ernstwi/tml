include "either.mc"
include "hashmap.mc"
include "json.mc"
include "string.mc"

-- Base language fragment, to be used in combination with other fragments. Not
-- valid as a stand-alone language.

-- Helper functions ------------------------------------------------------------

let insert = hashmapInsert hashmapStrTraits
let values = hashmapValues hashmapStrTraits
let lookup = hashmapLookup hashmapStrTraits

-- Unwrap a sequence of Options, discarding Nones.
let unwrap: [Option a] -> [a] =
    lam seq. map
        (lam ox. match ox with Some x then x else never)
        (filter (lam ox. match ox with Some _ then true else false) seq)

let edgeId: String -> String -> String =
    lam from. lam to. concat from (concat " -> " to)

let insertLocationIfUndefined:
    HashMap String Location -> String -> HashMap String Location =
    lam m. lam id.
    match lookup id m with None () then
        insert id { id = id, initial = false, invariant = None () } m
    else m

let stringSortCmp: (a -> String) -> (String -> String) =
    lam extractor. (lam l. lam r.
        if ltString (extractor l) (extractor r) then negi 1
        else if gtString (extractor l) (extractor r) then 1
        else 0)

let stringSort: [String] -> [String] = sort (stringSortCmp identity)

-- Types and syntactic forms ---------------------------------------------------

type Model = {
    locations: [Location],
    edges: [Edge],
    clocks: [String],
    actions: [String]
}

type Location = {
    id: String,
    initial: Boolean,
    invariant: Option Property
}

type Edge = {
    from: String,
    to: String,
    guard: Option Property,
    sync: Option Property,
    reset: Option Property
}

type ProgramRaw = [StatementRaw]
type ProgramCooked = [StatementCooked]
type InvariantConjunct = (String, Cmp, Int)
type PropertyModifier = Either Clear Property

type EvalEnv = {
    locations: HashMap String Location,
    edges: HashMap String Location,
    defaultInvariant: Option Property,
    defaultGuard: Option Property,
    defaultSync: Option Property,
    defaultReset: Option Property
}

lang Base
    syn StatementRaw =
    | LocationStmtRaw {
        id: String,
        initial: Boolean,
        properties: [PropertyModifier] }
    | EdgeStmtRaw {
        from: String,
        to: String,
        properties: [PropertyModifier] }
    | LocationDefaultRaw [PropertyModifier]
    | EdgeDefaultRaw [PropertyModifier]

    syn StatementCooked =
    | LocationStmtCooked {
        id: String,
        initial: Boolean,
        invariant: Option PropertyModifier
    }
    | EdgeStmtCooked {
        from: String,
        to: String,
        guard: Option PropertyModifier,
        sync: Option PropertyModifier,
        reset: Option PropertyModifier
    }
    | LocationDefaultCooked {
        invariant: Option PropertyModifier
    }
    | EdgeDefaultCooked {
        guard: Option PropertyModifier,
        sync: Option PropertyModifier,
        reset: Option PropertyModifier
    }

    syn Clear =
    | ClearInvariant ()
    | ClearGuard ()
    | ClearSync ()
    | ClearReset ()

    syn Property =
    | Invariant [InvariantConjunct]
    | Guard [GuardConjunct]
    | Sync Action
    | Reset [String]

    syn GuardConjunct =
    | OneClockGuard (String, Cmp, Int)
    | TwoClockGuard (String, String, Cmp, Int)

    syn Action = -- Empty syntactic construct, defined in extending fragments

    syn Cmp =
    | Lt ()
    | LtEq ()
    | Eq ()
    | GtEq ()
    | Gt ()

-- Validity checks -------------------------------------------------------------

    -- checkProperty: Property -> [String]
    sem checkProperty =
    | _ -> []

    -- checkPropertyModifier: PropertyModifier -> [String]
    sem checkPropertyModifier =
    | Left _ -> []
    | Right p -> checkProperty p

    -- repeatedProperties: String -> [PropertyModifier] -> [String]
    sem repeatedProperties (id: String) =
    | properties ->
        let errMsg: Int -> String -> [String] = lam n. lam s.
            if gti n 1 then
                [concat id (concat ": " (concat (int2string n) (concat " " s)))]
            else [] in
        concat (errMsg (length (filter (lam p.
            match p with Left (ClearInvariant ()) | Right (Invariant _)
            then true else false) properties)) "invariants")
        (concat (errMsg (length (filter (lam p.
            match p with Left (ClearGuard ()) | Right (Guard _)
            then true else false) properties)) "guards")
        (concat (errMsg (length (filter (lam p.
            match p with Left (ClearSync ()) | Right (Sync _)
            then true else false) properties)) "syncs")
        (errMsg (length (filter (lam p.
            match p with Left (ClearReset ()) | Right (Reset _)
            then true else false) properties)) "resets")))

    -- edgeProperties: String -> [PropertyModifier] -> [String]
    sem edgeProperties (id: String) =
    | properties ->
        match (find (lam p.
            match p with Left (ClearInvariant ()) | Right (Invariant _)
            then false else true) properties)
        with Some _ then [concat "Edge property on location " id] else []

    -- locationProperties: String -> [PropertyModifier] -> [String]
    sem locationProperties (id: String) =
    | properties ->
        match (find (lam p.
            match p with Left (ClearInvariant ()) | Right (Invariant _)
            then true else false) properties)
        with Some _ then [concat "Location property on edge " id] else []

    -- checkStatement: StatementRaw -> [String]
    sem checkStatement =
    | LocationStmtRaw { id = id, initial = _, properties = properties } ->
        concat (edgeProperties id properties)
        (concat (repeatedProperties id properties)
        (join (map checkPropertyModifier properties)))
    | EdgeStmtRaw { from = from, to = to , properties = properties } ->
        concat (locationProperties (edgeId from to) properties)
        (concat (repeatedProperties (edgeId from to) properties)
        (join (map checkPropertyModifier properties)))
    | LocationDefaultRaw properties ->
        concat (edgeProperties "default" properties)
        (concat (repeatedProperties "default location" properties)
        (join (map checkPropertyModifier properties)))
    | EdgeDefaultRaw properties ->
        concat (locationProperties "default" properties)
        (concat (repeatedProperties "default edge" properties)
        (join (map checkPropertyModifier properties)))

    -- checkProgram: ProgramRaw -> [String]
    --
    -- Check validity constraints on a ProgramRaw, returning a sequence of error
    -- messages.
    sem checkProgram =
    | statements ->
        join (cons
            (let inits = (length (filter
                (lam s. match s with LocationStmtRaw {
                    id = _,
                    initial = true,
                    properties = _ }
                then true else false) statements)) in
            if neqi inits 1 then
                [concat (int2string inits) " initial locations"] else [])
            (map checkStatement statements))

-- Cook ------------------------------------------------------------------------

    -- cookProperties:
    -- (PropertyModifier -> Boolean) -> [PropertyModifier] -> Option PropertyModifier
    sem cookProperties (f: PropertyModifier -> Boolean) =
    | properties ->
        let seq = filter f properties in
        if gti (length seq) 0 then
             -- We know from validity constraints that length of seq is 1
            Some (head seq)
        else
            None ()

    -- cookInvariant: [PropertyModifier] -> Option PropertyModifier
    sem cookInvariant =
    | properties -> cookProperties
        (lam p. match p with Left (ClearInvariant ()) | Right (Invariant _)
        then true else false) properties

    -- cookGuard: [PropertyModifier] -> Option PropertyModifier
    sem cookGuard =
    | properties -> cookProperties
        (lam p. match p with Left (ClearGuard ()) | Right (Guard _)
        then true else false) properties

    -- cookSync: [PropertyModifier] -> Option PropertyModifier
    sem cookSync =
    | properties -> cookProperties
        (lam p. match p with Left (ClearSync ()) | Right (Sync _)
        then true else false) properties

    -- cookReset: [PropertyModifier] -> Option PropertyModifier
    sem cookReset =
    | properties -> cookProperties
        (lam p. match p with Left (ClearReset ()) | Right (Reset _)
        then true else false) properties

    -- cookStatement: StatementRaw -> StatementCooked
    sem cookStatement =
    | LocationStmtRaw {
        id = id,
        initial = initial,
        properties = properties
    } -> LocationStmtCooked {
            id = id,
            initial = initial,
            invariant = cookInvariant properties
        }
    | EdgeStmtRaw {
        from = from,
        to = to,
        properties = properties
    } -> EdgeStmtCooked {
            from = from,
            to = to,
            guard = cookGuard properties,
            sync = cookSync properties,
            reset = cookReset properties
        }
    | LocationDefaultRaw properties ->
        LocationDefaultCooked { invariant = cookInvariant properties }
    | EdgeDefaultRaw properties ->
        EdgeDefaultCooked {
            guard = cookGuard properties,
            sync = cookSync properties,
            reset = cookReset properties
        }

    -- cookProgram: ProgramRaw -> ProgramCooked
    --
    -- Transform a raw parsed program to a cooked version, to prepare for
    -- evaluation.
    sem cookProgram =
    | statements -> map cookStatement statements

-- Evaluation ------------------------------------------------------------------

    -- getIdAction: Action -> String
    sem getIdAction =

    -- evalPropertyModifier: EvalEnv -> PropertyModifier -> Option Property
    sem evalPropertyModifier (env: EvalEnv) =
    | Left _ -> None ()
    | Right (Invariant i) -> Some (Invariant i)
    | Right (Guard g) -> Some (Guard g)
    | Right (Sync s) -> Some (Sync s)
    | Right (Reset r) -> Some (Reset r)

    -- evalOptionPropertyModifier:
    -- EvalEnv -> Option Property -> Option PropertyModifier -> Option Property
    sem evalOptionPropertyModifier (env: EvalEnv) (default: Option Property) =
    | Some e -> evalPropertyModifier env e
    | None () -> default

    -- evalStatement: EvalEnv -> StatementCooked -> EvalEnv
    sem evalStatement (env: EvalEnv) =
    | LocationStmtCooked {
        id = id,
        initial = initial,
        invariant = invariant
    } -> { env with locations =
            insert id {
                id = id,
                initial = initial,
                invariant =
                    evalOptionPropertyModifier env env.defaultInvariant invariant
            } env.locations
        }
    | EdgeStmtCooked {
        from = from,
        to = to,
        guard = guard,
        sync = sync,
        reset = reset
    } ->
        let newEdge: Edge = {
            from = from,
            to = to,
            guard = evalOptionPropertyModifier env env.defaultGuard guard,
            sync = evalOptionPropertyModifier env env.defaultSync sync,
            reset = evalOptionPropertyModifier env env.defaultReset reset
        } in
        let id = formatJson (jsonEdge newEdge) in
        {{{ env with edges = insert id newEdge env.edges
        } with locations = insertLocationIfUndefined env.locations from
        } with locations = insertLocationIfUndefined env.locations to }
    | LocationDefaultCooked { invariant = invariant } ->
        { env with defaultInvariant =
            evalOptionPropertyModifier env env.defaultInvariant invariant }
    | EdgeDefaultCooked {
        guard = guard,
        sync = sync,
        reset = reset
    } -> {{{ env with
        defaultGuard = evalOptionPropertyModifier env env.defaultGuard guard } with
        defaultSync = evalOptionPropertyModifier env env.defaultSync sync } with
        defaultReset = evalOptionPropertyModifier env env.defaultReset reset }

    -- evalProgram: ProgramCooked -> Model
    --
    -- Apply semantic rules on a Program, creating a Model.
    sem evalProgram =
    | statements ->
        let gatherClocks: [Location] -> [Edge] -> [String] =
            lam locations. lam edges.
            stringSort (distinct eqString (concat
                (join (map (lam l.
                    match l with { invariant = oi } then
                        match oi with Some (Invariant ics) then
                            map (lam ic.
                                match ic with (c, _, _) then
                                    c
                                else never) ics
                        else []
                    else never) locations))
                (join (map (lam e.
                    match e with { guard = og, reset = or} then
                        concat
                        (match og with Some (Guard gcs) then
                            join
                            (map (lam gc.
                                match gc with OneClockGuard (c, _, _) then
                                    [c]
                                else match gc with TwoClockGuard (c1, c2, _, _) then
                                    [c1, c2]
                                else never) gcs)
                        else [])
                        (match or with Some (Reset cs) then cs else [])
                    else never) edges)))) in

        let gatherActions: [Edge] -> [String] = lam edges.
            stringSort (distinct eqString (unwrap
                (map (lam e.
                    match e with { sync = os } then
                        match os with Some (Sync a) then
                            Some (getIdAction a)
                        else None ()
                    else never) edges))) in

        let env: EvalEnv = {
            locations = hashmapEmpty,
            edges = hashmapEmpty,
            defaultInvariant = None (),
            defaultGuard = None (),
            defaultSync = None (),
            defaultReset = None ()
        } in
        let res = foldl (lam e. lam s. evalStatement e s) env statements in
        let locations = sort
            (stringSortCmp (lam x. x.id))
            (values res.locations) in
        let edges = sort
            (stringSortCmp (lam x. formatJson (jsonEdge x)))
            (values res.edges) in
        let clocks = gatherClocks locations edges in
        let actions = gatherActions edges in
        { locations = locations, edges = edges, clocks = clocks, actions = actions }

-- Code generation -------------------------------------------------------------

    -- jsonAction: Action -> JsonValue
    sem jsonAction =

    sem jsonCmp =
    | Lt ()   -> "<"
    | LtEq () -> "<="
    | Eq ()   -> "=="
    | GtEq () -> ">="
    | Gt ()   -> ">"

    -- jsonProperty: Property -> JsonValue
    sem jsonProperty =
    | Invariant conjuncts ->
        JsonString (strJoin "&" (map (lam c.
            match c with (x, cmp, n) then
                concat x (concat (jsonCmp cmp) (int2string n))
            else never
        ) conjuncts))
    | Guard conjuncts ->
        JsonString (strJoin "&" (map (lam c.
            match c with OneClockGuard (x, cmp, n) then
                concat x (concat (jsonCmp cmp) (int2string n))
            else match c with TwoClockGuard (x, y, cmp, n) then
                concat (concat (concat x (concat "-" y)) (jsonCmp cmp))
                    (int2string n)
            else never
        ) conjuncts))
    | Sync action -> jsonAction action
    | Reset clocks -> JsonArray (map (lam c. JsonString c) clocks)

    -- jsonLocation: Location -> JsonValue
    sem jsonLocation =
    | { id = id, initial = initial, invariant = invariant } ->
        JsonObject [
            ("id", JsonString id),
            ("initial", JsonBool initial),
            ("invariant",
                match invariant with Some i then
                    jsonProperty i
                else JsonNull ()
            )
        ]

    -- jsonEdge: Edge -> JsonValue
    sem jsonEdge =
    | {
        from = from,
        to = to,
        guard = guard,
        sync = sync,
        reset = reset
    } ->
        JsonObject [
            ("from", JsonString from),
            ("to", JsonString to),
            ("guard",
                match guard with Some g then
                    jsonProperty g
                else JsonNull ()),
            ("sync",
                match sync with Some s then
                    jsonProperty s
                else JsonNull ()),
            ("reset",
                match reset with Some r then
                    jsonProperty r
                else JsonNull ())
        ]

    sem jsonActions =

    -- jsonModel: Model -> JsonValue
    --
    -- JSON representation of a Model.
    sem jsonModel =
    | { locations = locations, edges = edges, clocks = clocks, actions = actions } ->
        JsonObject [
            ("locations", JsonArray (map jsonLocation locations)),
            ("edges", JsonArray (map jsonEdge edges)),
            ("clocks", JsonArray (map (lam c. JsonString c) clocks)),
            jsonActions actions
        ]
end

-- Unit tests ------------------------------------------------------------------

mexpr use Base in

utest checkProgram [
    LocationStmtRaw {
        id = "foo",
        initial = true,
        properties = [Right (Reset ["x"])]
    }
] with ["Edge property on location foo"] in

utest checkProgram [
    LocationStmtRaw {
        id = "foo",
        initial = true,
        properties = []
    }, EdgeStmtRaw {
        from = "foo",
        to = "bar",
        properties = [Right (Reset ["x"]), Right (Invariant [])]
    }
] with ["Location property on edge foo -> bar"] in

utest checkProgram [] with ["0 initial locations"] in

utest checkProgram [
    LocationStmtRaw {
        id = "foo",
        initial = true,
        properties = [Right (Invariant []), Right (Invariant [])]
    }, EdgeStmtRaw {
        from = "foo",
        to = "bar",
        properties = [Right (Reset ["x"]), Right (Reset ["y"])]
    }
] with ["foo: 2 invariants", "foo -> bar: 2 resets"] in

utest checkProgram [
    LocationStmtRaw {
        id = "foo",
        initial = true,
        properties = []
    }, EdgeDefaultRaw [Right (Reset ["x"]), Right (Invariant [])]]
with ["Location property on edge default"] in

utest cookProgram [
    LocationStmtRaw {
        id = "foo",
        initial = true,
        properties = [Right (Invariant [("x", Lt (), 22)]) ]
    }, EdgeStmtRaw {
        from = "foo",
        to = "bar",
        properties = [
            Right (Guard [ OneClockGuard ("x", Gt (), 10) ]),
            Right (Reset [ "x" ])
        ]
    }
] with [
    LocationStmtCooked {
        id = "foo",
        initial = true,
        invariant = Some (Right (Invariant [("x", Lt (), 22)]))
    },
    EdgeStmtCooked {
        from = "foo",
        to = "bar",
        guard = Some (Right (Guard [ OneClockGuard ("x", Gt (), 10) ])),
        sync = None (),
        reset = Some (Right (Reset [ "x" ]))
    }
] in

utest evalProgram [
    LocationStmtCooked {
        id = "foo",
        initial = true,
        invariant = Some (Right (Invariant [("x", Lt (), 22)]))
    },
    LocationDefaultCooked {
        invariant = Some (Right (Invariant [("z", LtEq (), 100)]))
    },
    LocationStmtCooked {
        id = "bar",
        initial = false,
        invariant = Some (Right (Invariant [("y", Lt (), 44)]))
    },
    LocationStmtCooked {
        id = "baz",
        initial = false,
        invariant = None ()
    }
] with {
    locations = [
        {
            id = "bar",
            initial = false,
            invariant = Some (Invariant [("y", Lt (), 44)])
        },
        {
            id = "baz",
            initial = false,
            invariant = Some (Invariant [("z", LtEq (), 100)])
        },
        {
            id = "foo",
            initial = true,
            invariant = Some (Invariant [("x", Lt (), 22)])
        }
    ],
    edges = []
} in

()
