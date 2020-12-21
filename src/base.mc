include "either.mc"
include "hashmap.mc"
include "internal-action.mc"
include "json.mc"
include "string.mc"
include "sync-action.mc"
include "token.mc"

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

let insertLocationIfUndefined:
    EvalEnv -> HashMap String Location -> String -> HashMap String Location =
    lam env. lam m. lam id.
    match lookup id m with None () then
        insert id
            { id = id, initial = false, invariant = env.defaultInvariant } m
    else m

let stringSortCmp: (a -> String) -> (String -> String) =
    lam extractor. (lam l. lam r.
        if ltString (extractor l) (extractor r) then negi 1
        else if gtString (extractor l) (extractor r) then 1
        else 0)

let stringSort: [String] -> [String] = sort (stringSortCmp identity)

let seq2string: [String] -> String = lam seq.
    concat "[" (concat (strJoin ", " seq) "]")

let edgeId: [[String]] -> String =
    lam seq. strJoin " -> " (map seq2string seq)

let semanticError: String -> String -> String =
    lam statement. lam error. concat statement (concat ": " error)

let seqPairs: [a] -> [(a, a)] = lam seq.
    recursive let seqPairsHelper = lam seq.
        if eqi (length seq) 1 then []
    else
        concat [(head seq, head (tail seq))] (seqPairsHelper (tail seq)) in
    seqPairsHelper seq

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
    edges: HashMap String Edge,
    defaultInvariant: Option Property,
    defaultGuard: Option Property,
    defaultSync: Option Property,
    defaultReset: Option Property
}

lang Base
    syn StatementRaw =
    | LocationStmtRaw {
        ids: [String],
        initial: Boolean,
        properties: [PropertyModifier] }
    | EdgeStmtRaw {
        connections: [[String]],
        properties: [PropertyModifier] }
    | LocationDefaultRaw [PropertyModifier]
    | EdgeDefaultRaw [PropertyModifier]

    syn StatementCooked =
    | LocationStmtCooked {
        ids: [String],
        initial: Boolean,
        invariant: Option PropertyModifier
    }
    | EdgeStmtCooked {
        from: [String],
        to: [String],
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
                [semanticError id (concat (int2string n) (concat " " s))]
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
        with Some _ then
            [semanticError id "Edge property on location statement"]
        else []

    -- locationProperties: String -> [PropertyModifier] -> [String]
    sem locationProperties (id: String) =
    | properties ->
        match (find (lam p.
            match p with Left (ClearInvariant ()) | Right (Invariant _)
            then true else false) properties)
        with Some _ then [concat "Location property on edge " id] else []

    -- checkStatement: StatementRaw -> [String]
    sem checkStatement =
    | LocationStmtRaw { ids = ids, initial = _, properties = properties } ->
        concat (edgeProperties (seq2string ids) properties)
        (concat (repeatedProperties (seq2string ids) properties)
        (join (map checkPropertyModifier properties)))
    | EdgeStmtRaw { connections = connections, properties = properties } ->
        concat (locationProperties (edgeId connections) properties)
        (concat (repeatedProperties (edgeId connections) properties)
        (join (map checkPropertyModifier properties)))
    | LocationDefaultRaw properties ->
        concat (edgeProperties "[default location]" properties)
        (concat (repeatedProperties "[default location]" properties)
        (join (map checkPropertyModifier properties)))
    | EdgeDefaultRaw properties ->
        concat (locationProperties "[default edge]" properties)
        (concat (repeatedProperties "[default edge]" properties)
        (join (map checkPropertyModifier properties)))

    -- checkProgram: ProgramRaw -> [String]
    --
    -- Check validity constraints on a ProgramRaw, returning a sequence of error
    -- messages.
    sem checkProgram =
    | statements ->
        join (cons
            (let inits = (foldl addi 0 (map
                (lam s. match s with LocationStmtRaw {
                    ids = ids,
                    initial = true,
                    properties = _ }
                then (length ids) else 0) statements)) in
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
        ids = ids,
        initial = initial,
        properties = properties
    } -> LocationStmtCooked {
            ids = ids,
            initial = initial,
            invariant = cookInvariant properties
        }
    | EdgeStmtRaw {
        connections = connections,
        properties = properties
    } -> EdgeStmtCooked {
            connections = connections,
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
        ids = ids,
        initial = initial,
        invariant = invariant
    } ->
        let newLocations = foldl (lam locations. lam id.
            insert id {
                id = id,
                initial = initial,
                invariant =
                    evalOptionPropertyModifier env env.defaultInvariant invariant
                -- ^(optimization):
            } locations) env.locations ids in
        { env with locations = newLocations }
    | EdgeStmtCooked {
        connections = connections,
        guard = guard,
        sync = sync,
        reset = reset
    } ->
        let addedEdges = join (map (lam p. match p with (from, to) then
            join (map (lam f.
                map (lam t.  {
                    from = f,
                    to = t,
                    guard = evalOptionPropertyModifier env env.defaultGuard guard,
                    sync = evalOptionPropertyModifier env env.defaultSync sync,
                    reset = evalOptionPropertyModifier env env.defaultReset reset
                    -- ^(optimization):
                }) to
            ) from) else never) (seqPairs connections)) in

        let newEdges = foldl (lam edges. lam newEdge.
            insert (formatJson (jsonEdge newEdge)) newEdge edges
        ) env.edges addedEdges in

        {{ env with edges = newEdges }
               with locations = foldl
                   (lam locations. lam l. insertLocationIfUndefined env locations l)
                   env.locations (join connections) }
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

    -- action: Parser Action
    sem action =
end

-- Language compositions -------------------------------------------------------

-- TSA contains every "shallow" feature of TML (= features that can be compiled
-- to the base TSA model).
lang TSA = Base + InternalAction

-- TSA with input/output actions.
lang TsaSyncAction = Base + SyncAction

-- Parsers ---------------------------------------------------------------------

-- Parse one or more occurrences of `p` separated by single occurrences of `sep`.
let sepBy1: Parser s -> Parser a -> Parser [a] =
    lam sep. lam p.
    bind p (lam hd.
    bind (many (apr sep p)) (lam tl.
    pure (cons hd tl)))

--------------------------------------------------------------------------------

let lt:   Parser Cmp = use Base in bind (symbol "<")  (lam _. pure (Lt ()))
let ltEq: Parser Cmp = use Base in bind (symbol "<=") (lam _. pure (LtEq ()))
let eq:   Parser Cmp = use Base in bind (symbol "==") (lam _. pure (Eq ()))
let gtEq: Parser Cmp = use Base in bind (symbol ">=") (lam _. pure (GtEq ()))
let gt:   Parser Cmp = use Base in bind (symbol ">")  (lam _. pure (Gt ()))

--------------------------------------------------------------------------------

let cmp: Parser Cmp = use Base in
    alt eq (alt ltEq (alt lt (alt gtEq gt)))

let cmpInvar: Parser Cmp = use Base in
    alt ltEq lt

--------------------------------------------------------------------------------

let oneClockGuard: Parser GuardConjunct = use Base in
    bind identifier (lam a.
    bind cmp (lam c.
    bind number (lam n.
    pure (OneClockGuard (a, c, n)))))

let twoClockGuard: Parser GuardConjunct = use Base in
    bind identifier (lam a.
    bind (symbol "-") (lam _.
    bind identifier (lam b.
    bind cmp (lam c.
    bind number (lam n.
    pure (TwoClockGuard (a, b, c, n)))))))

--------------------------------------------------------------------------------

let invariantConjunct: Parser InvariantConjunct = use Base in
    bind identifier (lam id.
    bind cmpInvar (lam c.
    bind number (lam n.
    pure (id, c, n))))

let guardConjunct: Parser GuardConjunct = use Base in
    alt (try oneClockGuard) twoClockGuard

--------------------------------------------------------------------------------

let invariant: Parser PropertyModifier = use Base in
    bind (string "invar") (lam _.
    alt
    (bind (symbol "!") (lam _. pure (Left (ClearInvariant ()))))
    (bind (symbol "{") (lam _.
    bind (sepBy1 (symbol "&") invariantConjunct) (lam cs.
    bind (symbol "}") (lam _.
    pure (Right (Invariant cs)))))))


let guard: Parser PropertyModifier = use Base in
    bind (string "guard") (lam _.
    alt
    (bind (symbol "!") (lam _. pure (Left (ClearGuard ()))))
    (bind (symbol "{") (lam _.
    bind (sepBy1 (symbol "&") guardConjunct) (lam cs.
    bind (symbol "}") (lam _.
    pure (Right (Guard cs)))))))

let sync: Parser PropertyModifier = use SOURCE_LANG in
    bind (string "sync") (lam _.
    alt
    (bind (symbol "!") (lam _. pure (Left (ClearSync ()))))
    (bind (symbol "{") (lam _.
    bind (action ()) (lam a.
    bind (symbol "}") (lam _.
    pure (Right (Sync a)))))))

let reset: Parser PropertyModifier = use Base in
    bind (string "reset") (lam _.
    alt
    (bind (symbol "!") (lam _. pure (Left (ClearReset ()))))
    (bind (symbol "{") (lam _.
    bind (sepBy1 (symbol ",") identifier) (lam cs.
    bind (symbol "}") (lam _.
    pure (Right (Reset cs)))))))

--------------------------------------------------------------------------------

let property: Parser PropertyModifier = use Base in
    alt invariant (alt guard (alt sync reset))

--------------------------------------------------------------------------------

let locationDefault: Parser StatementRaw = use Base in
    bind (string "location") (lam _.
    bind (many property) (lam ps.
    pure (LocationDefaultRaw ps)))

let edgeDefault: Parser StatementRaw = use Base in
    bind (string "edge") (lam _.
    bind (many property) (lam ps.
    pure (EdgeDefaultRaw ps)))

--------------------------------------------------------------------------------

let locationSelector: Parser [String] = use Base in
    alt (bind identifier (lam id. pure [id]))
        (bind (symbol "[") (lam _.
        bind (sepBy1 (symbol ",") identifier) (lam ids.
        bind (symbol "]") (lam _.
        pure ids))))

let location: Parser StatementRaw = use Base in
    bind (optional (string "init")) (lam init.
    bind locationSelector (lam ids.
    bind (label "anything but ->" (notFollowedBy (symbol "->"))) (lam _.
    bind (many property) (lam ps.
    pure (LocationStmtRaw {
        ids = ids,
        initial = match init with Some _ then true else false,
        properties = ps
    })))))

let edge: Parser StatementRaw = use Base in
    bind locationSelector (lam c.
    bind (many1 (apr (symbol "->") locationSelector)) (lam cs.
    bind (many property) (lam ps.
    pure (EdgeStmtRaw {
        connections = cons c cs,
        properties = ps
    }))))

let default: Parser StatementRaw = use Base in
    bind (string "default") (lam _.
    alt locationDefault edgeDefault)

--------------------------------------------------------------------------------

let locationOrEdge: Parser StatementRaw = use Base in
    lam st.
    let res = location st in
    match res with Failure (_, "anything but ->", _) then
        edge st
    else res

--------------------------------------------------------------------------------

let statement: Parser StatementRaw = use Base in alt default locationOrEdge

--------------------------------------------------------------------------------

let program: Parser ProgramRaw = use Base in
    bind (many1 statement) (lam ss.
    bind (alt (apl (string "\n") endOfInput) endOfInput) (lam _.
    pure ss))
