include "string.mc"

include "ast.mc"

lang TmlCheck = TmlAst
    -- (question): Is there a way to type annotate interpreters?
    -- Expression -> [String]
    sem edgeProperties =
    | Properties properties -> foldl (lam n. lam p.
        match p with Guard _ then {n with guards = addi n.guards 1} else
        match p with Sync _ then {n with syncs = addi n.syncs 1} else
        match p with Reset _ then {n with resets = addi n.resets 1} else
        error "Malformed Properties")
        { guards = 0, syncs = 0, resets = 0 } properties

    | Edge (a, b, properties) ->
        let n = edgeProperties properties in

        let semErrString = lam a. lam b. lam n. lam s.
            concat "Semantic error: " (concat a (concat " -> " (concat b
            (concat ": " (concat (int2string n) (concat " " s)))))) in

        let semErrCheck = lam a. lam b. lam n. lam s.
            if gti n 1 then [semErrString a b n s] else [] in

        concat (semErrCheck a b n.guards "guards")
            (concat (semErrCheck a b n.syncs "syncs")
            (semErrCheck a b n.resets "resets"))
    | Program (_, edges) ->
        join (map (lam e. edgeProperties e) edges)

    -- Expression -> [String]
    sem initialLocation =
    | Program (locations, _) ->
        let iss = filter (lam l.
            match l with Location (_, initial, _) then
                initial
            else error "Malformed Location") locations in
        if neqi (length iss) 1 then
            [concat "Semantic error: " (concat (int2string (length iss)) " initial locations")]
        else []

    -- Expression -> [String]
    sem check =
    | Program p ->
        concat (initialLocation (Program p)) (edgeProperties (Program p))
        -- ^(question): Is there a way to get what we're matching on: Program p
end
