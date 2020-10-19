include "parser-combinators.mc"
include "json.mc"
include "../miking-ipm/src/models/modelVisualizer.mc"

-- Language definition ---------------------------------------------------------
-- EBNF variant: https://www.w3.org/TR/REC-xml/#sec-notation
--
-- Program    ::= state* transition*
-- state      ::= ("->")? id ("{" invar "}")?
-- transition ::= id "->" id props?
-- props      ::= ("guard {" guard "}")?
--                ("sync {" action "}")?
--                ("reset {" clocks "}")?
--
-- invar      ::= id ("<=" | "<") nat
-- guard      ::= constraint ("&&" constraint)*
-- constraint ::= id op nat | id "-" id op nat
-- op         ::= "<=" | "<" | "==" | ">" | ">="
-- action     ::= id /* To be extended for communication */
-- clocks     ::= id ("," id)*
--
-- id         ::= (letter | "_") (letter | "_" | digit)*
-- letter     ::= [a-zA-Z]
-- digit      ::= [0-9]
-- nat        ::= [1-9] digit*
--
-- Example:
-- -> foo
-- bar { x < 10 }
--
-- foo -> bar
--     guard { x - y == 5 && x > 2}
--     sync { a }
--     reset { x }
-- bar -> baz
--     reset { y }

-- Language fragment: AST definition + code generation (semantics) -------------

type Loc = String

lang TA
    syn Expr =
    | Trans (Loc, Loc)
    | Program [Trans]

    sem eval =
    | Program ts ->
        let states = map (lam s. JsonString s)
            (distinct eqString (join (map (lam t.
                match t with Trans (a, b) then
                    [a, b]
                else error "Not a transition") ts))) in
        let transitions = map (lam t. eval t) ts in
        JsonObject [
            ("states", JsonArray states),
            ("transitions", JsonArray transitions)]
    | Trans (a, b) ->
        JsonObject [
            ("from", JsonString a),
            ("to", JsonString b)]
end

-- Tokens (from stdlib) --------------------------------------------------------

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
let keywords = ["guard", "sync", "reset"]

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

utest showError (testParser identifier "guard")
with "Parse error at 1:1: Unexpected keyword 'guard'. Expected identifier"

utest testParser identifier "foo" with
Success ("foo", ("", {file="", row=1, col=4}))

-- Main parser -----------------------------------------------------------------

mexpr use TA in

let trans: Parser Trans =
    bind identifier (lam x.
    bind (symbol "->") (lam _.
    bind identifier (lam y.
    bind (symbol ";") (lam _.
    pure (Trans (x, y)))))) in

let program: Parser Program =
    bind (many trans) (lam ts.
    pure (Program ts)) in

-- Code generation -------------------------------------------------------------

let parseResult = testParser program (readFile "prototype/input") in
let ast = match parseResult with Success (x, _) then x else error "Parsing failed" in
let json = eval ast in
print (formatJson json)
