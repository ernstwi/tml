include "json.mc"
include "string.mc"

lang InternalAction
    syn Action =
    | InternalAction String

    -- checkAction: Action -> [String]
    sem checkAction =
    | InternalAction s ->
        if eqChar (head s) 'a' then
            []
        else
            [concat "Invalid InternalAction id: " s]

    -- jsonAction: Action -> JsonValue
    sem jsonAction =
    | InternalAction s -> JsonString s
end
