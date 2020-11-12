-- Semantic checks on AST phase 1. All functions take a Program and returns an
-- array of error message strings (if any).
--
-- (question): Is there a way to type annotate interpreters (sem)?

include "string.mc"
include "ast.mc"

lang TmlCheck = TmlAst
    -- Exactly one initial location
    sem initialLocation =
    | Program (locations, _, _, _) ->
        let iss = filter (lam l.
            match l with Location (_, initial, _) then
                initial
            else error "Malformed Location") locations in
        if neqi (length iss) 1 then
            [concat "Semantic error: " (concat (int2string (length iss)) " initial locations")]
        else []

    sem check =
    | Program p -> initialLocation (Program p)
        -- ^(question): Is there a way to get what we're matching on: Program p
end
