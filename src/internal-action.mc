include "json.mc"

lang InternalAction
    syn Action =
    | InternalAction String

    -- jsonAction: Action -> JsonValue
    sem jsonAction =
    | InternalAction id ->
        JsonObject [ ("type", JsonString "internal"), ("id", JsonString id) ]
end
