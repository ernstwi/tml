include "json.mc"
include "token.mc"

lang EdgeCtrl
    -- jsonEdge: Edge -> JsonValue
    sem jsonEdge =
    | {
        from = from,
        to = to,
        guard = guard,
        sync = sync,
        reset = reset,
        controllable = controllable
    } ->
        JsonObject [
            ("from", JsonString from),
            ("to", JsonString to),
            ("guard",
                match guard with Some g then
                    jsonProperty g
                else JsonNull ()),
            (actionKeyword (),
                match sync with Some s then
                    jsonProperty s
                else JsonNull ()),
            ("reset",
                match reset with Some r then
                    jsonProperty r
                else JsonNull ()),
            ("controllable", JsonBool controllable)
        ]

    -- connectionNode: () -> Parser ([String], Boolean)
    sem connectionNode = | _ ->
    bind (alt (symbol ">>") (symbol "->")) (lam arrow.
    bind (locationSelector ()) (lam l.
    pure (l, match arrow with "->" then true else false)))

    -- connections: () -> Parser [([String], Boolean)]
    sem connections = | _ ->
    bind (locationSelector ()) (lam c.
    bind (many1 (connectionNode ())) (lam cs.
    pure (cons (c, false) cs)))

    sem actionKeyword =
    sem jsonProperty =
    sem locationSelector =
end
