include "parser-combinators.mc"
include "../miking-ipm/src/models/modelVisualizer.mc"

-- AST  ------------------------------------------------------------------------

type Loc = String

type Statmt
con Trans : (Loc, Loc) -> Statmt

type Program = [Statmt]

-- Tokens ----------------------------------------------------------------------

let ws: Parser () = void (many spaces1)

-- `token p` parses `p` and any trailing whitespace or comments
let token: Parser a -> Parser a = lexToken ws

-- `string s` parses the string `s` as a token
let string: String -> Parser String = lam s. token (lexString s)
let symbol = string -- Alias

-- Check if a character is valid in an identifier
let isValidChar: Char -> Bool = lam c.
  or (isAlphanum c) (eqChar c '_')

let identifier: Parser String =
    bind (satisfy (lam c. or (isAlpha c) (eqChar '_' c)) "valid identifier") (lam c.
    -- ^ Identifiers must start with letter or underscore, not number
    bind (token (many (satisfy isValidChar ""))) (lam cs.
    pure (cons c cs)))

utest testParser identifier "foo" with
Success ("foo", ("", {file="", row=1, col=4}))

-- Main parser -----------------------------------------------------------------

let statmt: Parser Statmt =
    bind identifier (lam x.
    bind (symbol "->") (lam _.
    bind identifier (lam y.
    bind (symbol ";") (lam _.
    pure (Trans (x, y))))))

utest testParser statmt "foo -> bar;" with
Success (Trans ("foo", "bar"), ("", {file="", row=1, col=12}))

let main: Parser Program =
    many statmt

utest testParser main "foo -> bar; bar -> baz;" with
Success ([Trans ("foo", "bar"), Trans("bar", "baz")], ("", {file="", row=1, col=24}))

-- Code generation -------------------------------------------------------------

let parseResult = testParser main "foo -> bar; bar -> baz;"
let ast = match parseResult with Success (x, _) then x else error "Parsing failed"

let states = distinct eqString (join (map (lam t.
    match t with Trans (a, b) then
        [a, b]
    else error "Not a transition") ast))

utest states with ["foo", "bar", "baz"]

let transitions = map (lam t.
    match t with Trans (a, b) then
        (a, b, '0')
    else error "Not a transition") ast

utest transitions with [("foo", "bar", '0'), ("bar", "baz", '0')]

-- IPM invocation --------------------------------------------------------------

let startState = "foo"
let acceptStates = ["baz"]
let node2string = (lam x. x)
let label2string = (lam x. [x])

mexpr
let dfa = dfaConstr states transitions startState acceptStates eqString eqChar in

visualize [
	DFA(dfa,"00",node2string, label2string, "LR", [])
    -- ^ Arguments: data, input, node2str, label2str, direction, vSettings
]
