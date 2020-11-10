include "string.mc"

include "ast.mc"

lang TmlCheck = TmlAst
    -- (question): Is there a way to type annotate interpreters?
    -- Expression -> [String]
    sem transitionProperties =
    | Properties properties -> foldl (lam n. lam p.
        match p with Guard _ then {n with guards = addi n.guards 1} else
        match p with Sync _ then {n with syncs = addi n.syncs 1} else
        match p with Reset _ then {n with resets = addi n.resets 1} else
        error "Malformed Properties")
        { guards = 0, syncs = 0, resets = 0 } properties

    | Transition (a, b, properties) ->
        let n = transitionProperties properties in

        let semErrString = lam a. lam b. lam n. lam s.
            concat "Semantic error: " (concat a (concat " -> " (concat b
            (concat ": " (concat (int2string n) (concat " " s)))))) in

        let semErrCheck = lam a. lam b. lam n. lam s.
            if gti n 1 then [semErrString a b n s] else [] in

        concat (semErrCheck a b n.guards "guards")
            (concat (semErrCheck a b n.syncs "syncs")
            (semErrCheck a b n.resets "resets"))
    | Program (_, transitions) ->
        join (map (lam t. transitionProperties t) transitions)

    -- Expression -> [String]
    sem initialState =
    | Program (states, _) ->
        let iss = filter (lam s.
            match s with State (_, initial, _) then
                initial
            else error "Malformed State") states in
        if neqi (length iss) 1 then
            [concat "Semantic error: " (concat (int2string (length iss)) " initial states")]
        else []

    -- Expression -> [String]
    sem check =
    | Program p ->
        concat (initialState (Program p)) (transitionProperties (Program p))
        -- ^(question): Is there a way to get what we're matching on: Program p
end
