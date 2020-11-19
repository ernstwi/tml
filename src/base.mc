include "either.mc"
include "hashmap.mc"
include "json.mc"
include "string.mc"

-- Base language fragment, to be used in combination with other fragments. Not
-- valid as a stand-alone language.

-- Helper functions ------------------------------------------------------------

let insert = hashmapInsert hashmapStrTraits
let values = hashmapValues hashmapStrTraits

-- Unwrap a sequence of Options, discarding Nones.
let unwrap: [Option a] -> [a] =
    lam seq. map
        (lam ox. match ox with Some x then x else never)
        (filter (lam ox. match ox with Some _ then true else false) seq)

let edgeId: String -> String -> String =
    lam from. lam to. concat from (concat " -> " to)

-- Types and syntactic forms ---------------------------------------------------

type Model = {
    locations: [Location],
    edges: [Edge]
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

    -- checkAction: Action -> [String]
    sem checkAction =
    | _ -> never

    -- checkProperty: Property -> [String]
    sem checkProperty =
    | Sync a -> checkAction a
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
        concat (edgeProperties "default location" properties)
        (concat (repeatedProperties "default location" properties)
        (join (map checkPropertyModifier properties)))
    | EdgeDefaultRaw properties ->
        concat (locationProperties "default edge" properties)
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

    -- cookProperties: (Property -> Boolean) -> [Property] -> Option Property
    sem cookProperties (f: Property -> Boolean) =
    | properties ->
        let seq = filter f properties in
        if gti (length seq) 0 then
             -- We know from validity constraints that length of seq is 1
            Some (head seq)
        else
            None ()

    -- cookInvariant: [Property] -> Option Property
    sem cookInvariant =
    | properties -> cookProperties
        (lam p. match p with Left (ClearInvariant ()) | Right (Invariant _)
        then true else false) properties

    -- cookGuard: [Property] -> Option Property
    sem cookGuard =
    | properties -> cookProperties
        (lam p. match p with Left (ClearGuard ()) | Right (Guard _)
        then true else false) properties

    -- cookSync: [Property] -> Option Property
    sem cookSync =
    | properties -> cookProperties
        (lam p. match p with Left (ClearSync ()) | Right (Sync _)
        then true else false) properties

    -- cookReset: [Property] -> Option Property
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
    } -> let id = edgeId from to in
        -- ^(todo): Use tuple as key.
        { env with edges =
            insert id {
                from = from,
                to = to,
                guard =
                    evalOptionPropertyModifier env env.defaultGuard guard,
                sync =
                    evalOptionPropertyModifier env env.defaultSync sync,
                reset =
                    evalOptionPropertyModifier env env.defaultReset reset
            } env.edges
        }
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
        let env: EvalEnv = {
            locations = hashmapEmpty,
            edges = hashmapEmpty,
            defaultInvariant = None (),
            defaultGuard = None (),
            defaultSync = None (),
            defaultReset = None ()
        } in
        let res = foldl (lam e. lam s. evalStatement e s) env statements in
        {
            locations = sort
                (lam l. lam r. subi (string2int l.id) (string2int r.id))
                (values res.locations),
            edges = sort
                (lam l. lam r. subi (string2int (edgeId l.from l.to))
                (string2int (edgeId r.from r.to))) (values res.edges)
        }

-- Code generation -------------------------------------------------------------

    -- jsonAction: Action -> JsonValue
    sem jsonAction =
    | _ -> never

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

    -- jsonnEdge: Edge -> JsonValue
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

    -- jsonModel: Model -> JsonValue
    --
    -- JSON representation of a Model.
    sem jsonModel =
    | { locations = locations, edges = edges } ->
        JsonObject [
            ("locations", JsonArray (map jsonLocation locations)),
            ("edges", JsonArray (map jsonEdge edges))
        ]
end

-- Unit tests ------------------------------------------------------------------

mexpr use Base in

utest checkProgram [
    LocationStmtRaw {
        id = "foo",
        initial = true,
        properties = [Reset ["x"]]
    }
] with ["EdgeStmtRaw property on location foo"] in

utest checkProgram [
    LocationStmtRaw {
        id = "foo",
        initial = true,
        properties = []
    }, EdgeStmtRaw {
        from = "foo",
        to = "bar",
        properties = [Reset ["x"], Invariant []]
    }
] with ["LocationStmtRaw property on edge foo -> bar"] in

utest checkProgram [] with ["0 initial locations"] in

utest checkProgram [
    LocationStmtRaw {
        id = "foo",
        initial = true,
        properties = [ Invariant [], Invariant []]
    }, EdgeStmtRaw {
        from = "foo",
        to = "bar",
        properties = [Reset ["x"], Reset ["y"]]
    }
] with ["foo: 2 invariants", "foo -> bar: 2 resets"] in

utest checkProgram [
    LocationStmtRaw {
        id = "foo",
        initial = true,
        properties = []
    }, EdgeDefaultRaw [Reset ["x"], Invariant []]]
with ["LocationStmtRaw property on edge default"] in

utest cookProgram [
    LocationStmtRaw {
        id = "foo",
        initial = true,
        properties = [Invariant
            [("x", Lt (), 22)]
        ]
    }, EdgeStmtRaw {
        from = "foo",
        to = "bar",
        properties = [
            Guard [ OneClockGuard ("x", Gt (), 10) ],
            Reset [ "x" ]
        ]
    }
] with [
    LocationStmtCooked {
        id = "foo",
        initial = true,
        invariant = Some (Invariant [("x", Lt (), 22)])
    },
    EdgeStmtCooked {
        from = "foo",
        to = "bar",
        guard = Some (Guard [ OneClockGuard ("x", Gt (), 10) ]),
        sync = None (),
        reset = Some (Reset [ "x" ])
    }
] in

utest evalProgram [
    LocationStmtCooked {
        id = "foo",
        initial = true,
        invariant = Some (Invariant [("x", Lt (), 22)])
    },
    LocationDefaultCooked {
        invariant = Some (Invariant [("z", LtEq (), 100)])
    },
    LocationStmtCooked {
        id = "bar",
        initial = false,
        invariant = Some (Invariant [("y", Lt (), 44)])
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
