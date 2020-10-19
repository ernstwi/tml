include "parser-combinators.mc"
include "../miking-ipm/src/models/modelVisualizer.mc"


-- Language fragment: AST definition + code generation (semantics) -------------

type Loc = String

lang TA
    syn Expr =
    | Trans (Loc, Loc)
    | Program [Trans]

    sem eval =
    | Trans (a, b) -> (a, b, '0')
    | Program ts ->
        let states = distinct eqString (join (map (lam t.
            match t with Trans (a, b) then
                [a, b]
            else error "Not a transition") ts)) in
        let transitions = map (lam t. eval t) ts in
        let startState = "foo" in
        let acceptStates = ["baz"] in
        dfaConstr states transitions startState acceptStates eqString eqChar
end

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

let parseResult = testParser program "foo -> bar; bar -> baz;" in
let ast = match parseResult with Success (x, _) then x else error "Parsing failed" in
let dfa = eval ast in

-- IPM invocation --------------------------------------------------------------

let node2string = (lam x. x) in
let label2string = (lam x. [x]) in

visualize [
	DFA(dfa,"00",node2string, label2string, "LR", [])
    -- ^ Arguments: data, input, node2str, label2str, direction, vSettings
]
