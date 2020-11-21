include "json.mc"

lang InternalAction
    syn Action =
    | InternalAction String

    -- jsonAction: Action -> JsonValue
    sem jsonAction =
    | InternalAction id ->
        JsonObject [ ("type", JsonString "internal"), ("id", JsonString id) ]

    -- jsonActions: [String] -> JsonValue
    sem jsonActions =
    | actions -> ("actions", JsonArray (map (lam a. JsonString a) actions))

    sem getIdAction =
    | InternalAction id -> id
end
