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
-- guard      ::= id op nat | id "-" id op nat
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
--     guard { x - y == 5 }
--     sync { a }
--     reset { x }
-- bar -> baz
--     reset { y }

-- Language fragment: AST definition + code generation (semantics) -------------

lang TA
    syn Cmp =
    | Lt ()
    | LtEq ()

    syn Expression =
    | Invariant (String, Cmp, Int)
    | State (String, Boolean, Option Invariant)
    | Program [State]

    sem eval =
    | Invariant (x, cmp, n) ->
        JsonString (concat x
            (concat (match cmp with Lt () then "<" else "<=") (int2string n)))
    | State (id, initial, invariant) ->
        JsonObject [
            ("id", JsonString id),
            ("initial", JsonBool initial),
            ("invariant", match invariant with Some inv then eval inv else JsonNull ())]
    | Program states ->
        JsonArray (map (lam s. eval s) states)
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

let lt: Parser Cmp = bind (symbol "<") (lam _. pure (Lt ())) in
let ltEq: Parser Cmp = bind (symbol "<=") (lam _. pure (LtEq ())) in
let cmp: Parser Cmp = alt (try ltEq) lt in

let invariant: Parser Expr =
    bind (symbol "{") (lam _.
    bind identifier (lam id.
    bind cmp (lam c.
    bind number (lam n.
    bind (symbol "}") (lam _.
    pure (Invariant (id, c, n))))))) in

let state: Parser Expr =
    bind (optional (symbol "->")) (lam init.
    bind identifier (lam id.
    bind (optional invariant) (lam invar.
    pure (State (id, match init with Some _ then true else false, invar))))) in

let program: Parser Expr =
    bind (many state) (lam ss.
    pure (Program ss)) in

-- Code generation -------------------------------------------------------------

let parseResult = testParser program (readFile "prototype/input") in
let ast = match parseResult with Success (x, _) then x else error "Parsing failed" in
let json = eval ast in
let _ = print (formatJson json) in

-- Tests -----------------------------------------------------------------------

utest testParser cmp "<" with
Success (Lt (), ("", {file="", row=1, col=2})) in

utest testParser cmp "<=" with
Success (LtEq (), ("", {file="", row=1, col=3})) in

utest testParser invariant "{ x < 10 }" with
Success(Invariant ("x", Lt (), 10), ("", {file="", row=1, col=11})) in

utest eval (Invariant ("x", Lt (), 10)) with
JsonString ("x<10") in

utest testParser state "bar { x < 10 }" with
Success(State ("bar", false, Some (Invariant ("x", Lt (), 10))), ("", {file="", row=1, col=15})) in

utest eval (State ("bar", false, Some (Invariant ("x", Lt (), 10)))) with
JsonObject [
    ("id", JsonString "bar"),
    ("initial", JsonBool false),
    ("invariant", JsonString "x<10")] in

utest testParser state "-> foo" with
Success(State ("foo", true, None ()), ("", {file="", row=1, col=7})) in

utest testParser program "-> foo bar { x < 10 }" with
Success(Program [
    State ("foo", true, None ()),
    State ("bar", false, Some (Invariant ("x", Lt (), 10)))],
    ("", {file="", row=1, col=22})) in
()
