include "string.mc"
include "tsa-base.mc"

lang TsaRaw = TsaBase
    syn Expression =
    | Program {
        locations: [Location],
        edges: [Edge],
        defaultInvariant: Option Invariant,
        defaultGuard: Option Guard,
        defaultSync: Option Sync,
        defaultReset: Option Reset
    }

    syn Default =
    | LocationDefault (Option Expression)
    | EdgeDefault (Option Expression, Option Expression, Option Expression)

    sem check =
    | Program p -> initialLocation (Program p)
        -- ^(question): Is there a way to get what we're matching on: Program p

    -- Exactly one initial location
    sem initialLocation =
    | Program (locations, _, _, _) ->
        let iss = filter (lam l.
            match l with Location (_, initial, _) then
                initial
            else error "Malformed Location") locations in
        if neqi (length iss) 1 then
            [concat "Semantic error: " (concat (int2string (length iss)) " initial locations")]
        else []
end
