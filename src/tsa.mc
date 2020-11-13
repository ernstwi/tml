lang TSA = TsaRaw + TsaCooked
    sem transform =
    | Program p -> applyDefaults (Program p)

    sem applyDefaults =
    | Program (locations, edges, defaultInvariant, defaultGuard, defaultSync, defaultReset) ->
        let newLocations =
            map (lam l.
                match l with Location (id, initial, oi) then
                    Location (id, initial,
                        match oi with Some _ then oi else defaultInvariant)
                else never) locations in
        let newEdges =
            map (lam e.
                match e with Edge (from, to, og, os, or) then
                    Edge (from, to,
                        match og with Some _ then og else defaultGuard,
                        match os with Some _ then os else defaultSync,
                        match or with Some _ then or else defaultReset)
                else never) edges in
        Program (newLocations, newEdges)
end

