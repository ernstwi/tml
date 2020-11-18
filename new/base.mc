include "string.mc"

-- Base language fragment, to be used in combination with other fragments. Not
-- valid as a stand-alone language.

-- Unwrap a sequence of Options, discarding Nones.
let unwrap: [Option a] -> [a] =
    lam seq. map
        (lam ox. match ox with Some x then x else never)
        (filter (lam ox. match ox with Some _ then true else false) seq)

type Model = ([Location], [Edge])
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
    | _ -> []

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
    | LocationStmtRaw (id, _, properties) ->
        concat
        (match (find (lam p.
            match p with Invariant _ then false else true) properties)
        with Some _ then [concat "EdgeStmtRaw property on location " id] else [])
        (repeatedProperties id properties)
    | EdgeStmtRaw (from, to, properties) ->
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
                (lam s. match s with LocationStmtRaw (_, true, _) then true
                else false) statements)) in
            if neqi inits 1 then
                [concat (int2string inits) " initial locations"] else [])
            (map checkStatement statements))

-- Cook ------------------------------------------------------------------------

    -- cookProgram: ProgramRaw -> ProgramCooked
    --
    -- Transform a raw parsed program to a cooked version, to prepare for
    -- evaluation.
    -- sem cookProgram =

-- Evaluation ------------------------------------------------------------------

    -- evalProgram: ProgramCooked -> Model
    --
    -- Apply semantic rules on a Program, creating a Model.
    -- sem evalProgram =

-- Code generation -------------------------------------------------------------

    -- jsonModel: Model -> JsonValue
    --
    -- JSON representation of a Model.
    -- sem jsonModel =
end

mexpr
use Base in
utest checkProgram [LocationStmtRaw ("foo", true, [Reset ["x"]])] with ["EdgeStmtRaw property on location foo"] in
utest checkProgram [LocationStmtRaw ("foo", true, []), EdgeStmtRaw ("foo", "bar", [Reset ["x"], Invariant []])] with ["LocationStmtRaw property on edge foo -> bar"] in
utest checkProgram [] with ["0 initial locations"] in
utest checkProgram [LocationStmtRaw ("foo", true, [ Invariant [], Invariant []]), EdgeStmtRaw ("foo", "bar", [Reset ["x"], Reset ["y"]])] with ["foo: 2 invariants", "foo -> bar: 2 resets"] in
utest checkProgram [LocationStmtRaw ("foo", true, []), EdgeDefaultRaw [Reset ["x"], Invariant []]] with ["LocationStmtRaw property on edge default"] in
()
