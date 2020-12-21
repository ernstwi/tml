include "json.mc"
include "token.mc"

lang SyncAction
    syn Action =
    | InputAction String
    | OutputAction String

    -- jsonAction: Action -> JsonValue
    sem jsonAction =
    | InputAction id ->
        JsonObject [ ("type", JsonString "input"), ("id", JsonString id) ]
    | OutputAction id ->
        JsonObject [ ("type", JsonString "output"), ("id", JsonString id) ]

    -- jsonActions: [String] -> JsonValue
    sem jsonActions =
    | channels -> ("channels", JsonArray (map (lam c. JsonString c) channels))

    -- getIdAction: Action -> String
    sem getIdAction =
    | InputAction id -> id
    | OutputAction id -> id

    -- action: () -> Parser Action
    sem action = | _ ->
    bind identifier (lam id.
    alt (apr (symbol "?") (pure (InputAction id)))
        (apr (symbol "!") (pure (OutputAction id))))

    -- actionKeyword: () -> String
    sem actionKeyword = | _ -> "sync"
end
