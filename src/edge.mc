include "json.mc"
include "token.mc"

lang Edge
    sem jsonProperty =

    -- jsonEdge: Edge -> JsonValue
    sem jsonEdge =
    | {
        from = from,
        to = to,
        guard = guard,
        sync = sync,
        reset = reset,
        controllable = _
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
                else JsonNull ())
        ]

    sem locationSelector =

    -- connections: Parser [([String], Boolean)]
    sem connections = | _ ->
    bind (locationSelector ()) (lam c.
    bind (many1 (apr (symbol "->") (locationSelector ()))) (lam cs.
    pure (cons (c, false) (map (lam x. (x, false)) cs))))

    sem actionKeyword =
end
