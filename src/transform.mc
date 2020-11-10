include "ast.mc"

lang TmlTransform = TmlAst
    -- Expression -> Expression, with the change
    --     Properties [ Guard | Sync | Reset ] ->
    --     Properties (Optional Guard, Optional Sync, Optional Reset)
    -- to simplify code generation.
    sem transform =
    | Properties properties ->
        -- At this point we know that properties contains at most one of each
        let o = foldl (lam o. lam p.
            match p with Guard _ then {o with g = Some p} else
            match p with Sync _ then {o with s = Some p} else
            match p with Reset _ then {o with r = Some p} else
            error "Malformed Properties")
            {g = None (), s = None (), r = None ()} properties in
        Properties (o.g, o.s, o.r)
    | Edge (a, b, properties) ->
        Edge (a, b, transform properties)
    | Program (locations, edges) ->
        Program (locations, map transform edges)
end
