include "parser-combinators.mc"

-- Tokenizers (from stdlib) ----------------------------------------------------

let ws: Parser () = void (many spaces1)

-- `token p` parses `p` and any trailing whitespace or comments
let token: Parser a -> Parser a = lexToken ws

-- `string s` parses the string `s` as a token
let string: String -> Parser String = lam s. token (lexString s)
let symbol = string -- Alias

-- Check if a character is valid in an identifier
let isValidChar: Char -> Bool = lam c.
  or (isAlphanum c) (eqChar c '_')

-- Parse a specific string and fail if it is followed by
-- additional valid identifier characters.
let reserved: String -> Parser () = lam s.
  void (token (apl (lexString s) (notFollowedBy (satisfy isValidChar ""))))

let number: Parser Int = token lexNumber

-- List of reserved keywords
let keywords = ["init", "invar", "guard", "sync", "reset"]

-- Parse an identifier, but require that it is not in the list
-- of reserved keywords.
let identifier: Parser String =
  let validId =
    bind (satisfy (lam c. or (isAlpha c) (eqChar '_' c)) "valid identifier") (lam c.
    -- ^ Identifiers must start with letter or underscore, not number
    bind (token (many (satisfy isValidChar ""))) (lam cs.
    pure (cons c cs)))
  in
  try (
    bind validId (lam x.
    if any (eqString x) keywords
    then fail (concat (concat "keyword '" x) "'") "identifier"
    else pure x)
  )

-- Unit tests ------------------------------------------------------------------

utest showError (testParser identifier "guard")
with "Parse error at 1:1: Unexpected keyword 'guard'. Expected identifier"

utest testParser identifier "foo" with
Success ("foo", ("", {file="", row=1, col=4}))
