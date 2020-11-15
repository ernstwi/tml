include "string.mc"

-- Base language fragment, to be used in combination with other fragments. Not
-- valid as a stand-alone language.

-- Unwrap a sequence of Options, discarding Nones.
let unwrap: [Option a] -> [a] =
    lam seq. map
        (lam ox. match ox with Some x then x else never)
        (filter (lam ox. match ox with Some _ then true else false) seq)


type Program = [Statement]
type InvariantConjunct = (String, Cmp, Int)

lang Base
    syn Statement =
    | Location {
        id: String,
        initial: Boolean,
        properties: [Property] }
    | Edge {
        from: String,
        to: String,
        properties: [Property] }
    | LocationDefault [Property]
    | EdgeDefault [Property]

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

    -- checkAction: Action -> [String]
    sem checkAction =
    | _ -> []

    -- checkProperty: Property -> [String]
    sem checkProperty =
    | Sync a -> checkAction a
    | _ -> []

    -- checkStatement: Statement -> [String]
    sem checkStatement =
    | Location (id, _, properties) ->
        match (find (lam p.
            match p with Invariant _ then false else true) properties)
            with Some _ then [concat "Edge property on location " id]
            else []
    | Edge (from, to, properties) ->
        concat
            (match (find
                (lam p.  match p with Invariant _ then true else false)
                properties
            ) with Some _ then
                [concat "Location property on edge " (concat from
                    (concat " -> " to))]
            else [])
            (join (map checkProperty properties))

    -- checkProgram: Program -> [String]
    --
    -- Check validity constraints on a Program, returning a sequence of error
    -- messages.
    sem checkProgram =
    | statements ->
        join (cons
            (let inits = (length (filter
                (lam s. match s with Location (_, true, _) then true
                else false) statements)) in
            if neqi inits 1 then
                [concat (int2string inits) " initial locations"] else [])
            (map checkStatement statements))
end

mexpr
use Base in
utest checkProgram [Location ("foo", true, [Reset ["x"]])] with ["Edge property on location foo"] in
utest checkProgram [Location ("foo", true, []), Edge ("foo", "bar", [Reset ["x"], Invariant []])] with ["Location property on edge foo -> bar"] in
utest checkProgram [] with ["0 initial locations"] in
()
