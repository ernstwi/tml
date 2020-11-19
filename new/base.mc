include "hashmap.mc"
include "json.mc"
include "string.mc"

-- Base language fragment, to be used in combination with other fragments. Not
-- valid as a stand-alone language.

-- Unwrap a sequence of Options, discarding Nones.
let unwrap: [Option a] -> [a] =
    lam seq. map
        (lam ox. match ox with Some x then x else never)
        (filter (lam ox. match ox with Some _ then true else false) seq)

let insert = hashmapInsert hashmapStrTraits
let values = hashmapValues hashmapStrTraits

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

type EvalEnv = {
    locations: HashMap String Location,
    edges: HashMap (String, String) Location,
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
        properties: [Property] }
    | EdgeStmtRaw {
        from: String,
        to: String,
        properties: [Property] }
    | LocationDefaultRaw [Property]
    | EdgeDefaultRaw [Property]

    syn StatementCooked =
    | LocationStmtCooked {
        id: String,
        initial: Boolean,
        invariant: Option Property
    }
    | EdgeStmtCooked {
        from: String,
        to: String,
        guard: Option Property,
        sync: Option Property,
        reset: Option Property
    }
    | LocationDefaultCooked {
        invariant: Option Property
    }
    | EdgeDefaultCooked {
        guard: Option Property,
        sync: Option Property,
        reset: Option Property
    }

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

    -- repeatedProperties: String -> [Property] -> [String]
    sem repeatedProperties (id: String) =
    | properties ->
        let errMsg: Int -> String -> [String] = lam n. lam s.
            if gti n 1 then
                [concat id (concat ": " (concat (int2string n) (concat " " s)))]
            else [] in
        concat (errMsg (length (filter (lam p.
            match p with Invariant _ then true else false) properties)) "invariants")
        (concat (errMsg (length (filter (lam p.
            match p with Guard _ then true else false) properties)) "guards")
        (concat (errMsg (length (filter (lam p.
            match p with Sync _ then true else false) properties)) "syncs")
        (errMsg (length (filter (lam p.
            match p with Reset _ then true else false) properties)) "resets")))

    -- checkStatement: StatementRaw -> [String]
    sem checkStatement =
    | LocationStmtRaw { id = id, initial = _, properties = properties } ->
        concat
        (match (find (lam p.
            match p with Invariant _ then false else true) properties)
        with Some _ then [concat "EdgeStmtRaw property on location " id] else [])
        (repeatedProperties id properties)
    | EdgeStmtRaw { from = from, to = to , properties = properties } ->
        concat
        (match (find
            (lam p.  match p with Invariant _ then true else false)
            properties
        ) with Some _ then
            [concat "LocationStmtRaw property on edge " (concat from
                (concat " -> " to))] else [])
        (concat
        (repeatedProperties (concat from (concat " -> " to)) properties)
        (join (map checkProperty properties)))
    | LocationDefaultRaw properties ->
        concat
        (match (find (lam p.
            match p with Invariant _ then false else true) properties)
        with Some _ then ["EdgeStmtRaw property on location default"] else [])
        (repeatedProperties "default location" properties)
    | EdgeDefaultRaw properties ->
        concat
        (match (find
            (lam p.  match p with Invariant _ then true else false)
            properties
        ) with Some _ then
            ["LocationStmtRaw property on edge default"] else [])
        (concat
        (repeatedProperties "default edge" properties)
        (join (map checkProperty properties)))

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
    | properties ->
        cookProperties
            (lam p. match p with Invariant _ then true else false)
            properties

    -- cookGuard: [Property] -> Option Property
    sem cookGuard =
    | properties ->
        cookProperties
            (lam p. match p with Guard _ then true else false)
            properties

    -- cookSync: [Property] -> Option Property
    sem cookSync =
    | properties ->
        cookProperties
            (lam p. match p with Sync _ then true else false)
            properties

    -- cookReset: [Property] -> Option Property
    sem cookReset =
    | properties ->
        cookProperties
            (lam p. match p with Reset _ then true else false)
            properties

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
                    match invariant with Some _ then
                        invariant
                    else env.defaultInvariant
            } env.locations
        }
    | EdgeStmtCooked {
        from = from,
        to = to,
        guard = guard,
        sync = sync,
        reset = reset
    } -> let id = concat from (concat " -> " to) in
        -- ^(todo): Use tuple as key.
        { env with edges =
            insert id {
                from = from,
                to = to,
                guard = match guard with Some _ then guard else env.defaultGuard,
                sync = match sync with Some _ then sync else env.defaultSync,
                reset = match reset with Some _ then reset else env.defaultReset
            } env.edges
        }
    | LocationDefaultCooked { invariant = oi } ->
        match oi with Some i then { env with defaultInvariant = oi }
        else env
    | EdgeDefaultCooked {
        guard = og,
        sync = os,
        reset = or
    } ->
        let ng = match og with Some g then og else env.defaultGuard in
        let ns = match os with Some s then os else env.defaultSync in
        let nr = match or with Some r then or else env.defaultReset in
        {{{ env with defaultGuard = ng } with defaultSync = ns }
            with defaultReset = nr }

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
        { locations = values res.locations, edges = values res.edges }

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
            id = "foo",
            initial = true,
            invariant = Some (Invariant [("x", Lt (), 22)])
        },
        {
            id = "baz",
            initial = false,
            invariant = Some (Invariant [("z", LtEq (), 100)])
        },
        {
            id = "bar",
            initial = false,
            invariant = Some (Invariant [("y", Lt (), 44)])
        }
    ],
    edges = []
} in
-- ^(note): Sorting of locations, edges, is undefined.

()
