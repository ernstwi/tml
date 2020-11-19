include "json.mc"

lang InternalAction
    syn Action =
    | InternalAction String

    -- jsonAction: Action -> JsonValue
    sem jsonAction =
    | InternalAction s -> JsonString s
end
