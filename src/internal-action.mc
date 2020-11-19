include "json.mc"

lang InternalAction
    syn Action =
    | InternalAction String

    -- checkAction: Action -> [String]
    sem checkAction =
    | InternalAction s -> []

    -- jsonAction: Action -> JsonValue
    sem jsonAction =
    | InternalAction s -> JsonString s
end
