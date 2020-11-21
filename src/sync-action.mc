include "json.mc"

lang SyncAction
    syn Action =
    | InputAction String
    | OutputAction String

    sem jsonAction =
    | InputAction id ->
        JsonObject [ ("type", JsonString "input"), ("id", JsonString id) ]
    | OutputAction id ->
        JsonObject [ ("type", JsonString "output"), ("id", JsonString id) ]

    -- jsonActions: [String] -> JsonValue
    sem jsonActions =
    | channels -> ("channels", JsonArray (map (lam c. JsonString c) channels))

    sem getIdAction =
    | InputAction id -> id
    | OutputAction id -> id
end
