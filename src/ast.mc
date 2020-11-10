lang TmlAst
    syn Cmp =
    | Lt ()
    | LtEq ()
    | Eq ()
    | GtEq ()
    | Gt ()

    sem cmp2string =
    | Lt () -> "<"
    | LtEq () -> "<="
    | Eq () -> "=="
    | GtEq () -> ">="
    | Gt () -> ">"

    syn Expression =
    | Reset [String]
    | Sync String
    | TwoClockGuard (String, String, Cmp, Int)
    | OneClockGuard (String, Cmp, Int)
    | GuardConjunct (Either OneClockGuard TwoClockGuard)
    | Guard [GuardConjunct]
    | Properties (Option Guard, Option Sync, Option Reset)
    | Properties [Expression]
    -- ^(todo): Can we have a more descriptive type here?
    --          What I mean: [Guard | Sync | Reset]
    --
    -- ^(question): Overloaded constructor name `Properties` - is this allowed?
    | Edge (String, String, Properties)
    | InvariantConjunct (String, Cmp, Int)
    | Invariant [InvariantConjunct]
    | Location (String, Boolean, Option Invariant)
    | Program ([Location], [Edge])
end
