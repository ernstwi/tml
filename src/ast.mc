lang TmlAst
    syn Cmp =
    | Lt ()
    | LtEq ()
    | Eq ()
    | GtEq ()
    | Gt ()

    syn Expression =
    | Program { -- Phase 1
        locations: [Location],
        edges: [Edge],
        defaultInvariant: Option Invariant,
        defaultGuard: Option Guard,
        defaultSync: Option Sync,
        defaultReset: Option Reset
    }

    | Program { -- Phase 2
        locations: [Location],
        edges: [Edge]
    }

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

    syn Default =
    | LocationDefault (Option Expression)
    | EdgeDefault (Option Expression, Option Expression, Option Expression)
end
