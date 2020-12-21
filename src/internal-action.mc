include "json.mc"
include "token.mc"

lang InternalAction
    syn Action =
    | InternalAction String

    -- jsonAction: Action -> JsonValue
    sem jsonAction =
    | InternalAction id -> JsonString id

    -- jsonActions: [String] -> JsonValue
    sem jsonActions =
    | actions -> ("actions", JsonArray (map (lam a. JsonString a) actions))

    sem getIdAction =
    | InternalAction id -> id

    -- action: Parser Action
    sem action = | _ ->
    bind identifier (lam id.
    pure (InternalAction id))

    sem actionKeyword = | _ -> "action"
end
