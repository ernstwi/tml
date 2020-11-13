lang TsaBase
    syn Cmp =
    | Lt ()
    | LtEq ()
    | Eq ()
    | GtEq ()
    | Gt ()

    syn Expression =
    | Location {
        id: String,
        initial: Boolean,
        invariant: Option Invariant
    }
    | Edge {
        from: String,
        to: String,
        guard: Option Guard,
        sync: Option Sync,
        reset: Option Reset
    }
    | Reset [String]
    | Sync String
    | TwoClockGuard (String, String, Cmp, Int)
    | OneClockGuard (String, Cmp, Int)
    | GuardConjunct (Either OneClockGuard TwoClockGuard)
    | Guard [GuardConjunct]
    | InvariantConjunct (String, Cmp, Int)
    | Invariant [InvariantConjunct]
end
