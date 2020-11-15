-- Base language fragment, to be used in combination with other fragments.

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
    | Sync Action -- Defined in extension
    | Reset [String]

    syn GuardConjunct =
    | OneClockGuard (String, Cmp, Int)
    | TwoClockGuard (String, String, Cmp, Int)

    syn Cmp =
    | Lt ()
    | LtEq ()
    | Eq ()
    | GtEq ()
    | Gt ()
end
