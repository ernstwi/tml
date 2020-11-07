include "parser-combinators.mc"
include "json.mc"
include "either.mc"

-- Language definition ---------------------------------------------------------

-- EBNF variant: https://www.w3.org/TR/REC-xml/#sec-notation
--
-- Program    ::= (state | transition)*
--
-- state      ::= "init"? id ("invar {" invars "}")?
--
-- invars     ::= invar ("&" invar)*
-- invar      ::= id ("<=" | "<") nat
--
-- transition ::= id "->" id props
-- props      ::= ("guard {" guards "}")?
--                ("sync {" action "}")?
--                ("reset {" clocks "}")?
--
-- guards     ::= guard ("&" guard)*
-- guard      ::= (id op nat) | (id "-" id op nat)
-- op         ::= "<=" | "<" | "==" | ">" | ">="
--
-- action     ::= id /* To be extended for communication */
-- clocks     ::= id ("," id)*
--
-- id         ::= (letter | "_") (letter | "_" | digit)*
-- letter     ::= [a-zA-Z]
-- digit      ::= [0-9]
-- nat        ::= [1-9] digit*
--
-- Example:
-- init foo
-- bar { x < 10 }
--
-- foo -> bar
--     guard { x - y == 5 }
--     sync { a }
--     reset { x }
-- bar -> baz
--     reset { y }
--
-- Possible improvements:
-- • Allow any order of properties (guard, sync, reset)
--
-- Semantic rules:
-- • Exactly one initial state

-- Language fragment: AST definition + code generation (semantics) -------------

lang TA
    syn Cmp =
    | Lt ()
    | LtEq ()
    | Eq ()
    | GtEq ()
    | Gt ()

    sem cmp2string =
    | Lt () -> "<"
    | LtEq () -> "<="
    | Eq () -> "=="
    | GtEq () -> ">="
    | Gt () -> ">"

    syn Expression =
    | Reset [String]
    | Sync String
    | TwoClockGuard (String, String, Cmp, Int)
    | OneClockGuard (String, Cmp, Int)
    | GuardConjunct (Either OneClockGuard TwoClockGuard)
    | Guard [GuardConjunct]
    | Properties (Option Guard, Option Sync, Option Reset)
    | Transition (String, String, Properties)
    | InvariantConjunct (String, Cmp, Int)
    | Invariant [InvariantConjunct]
    | State (String, Boolean, Option Invariant)
    | Program ([State], [Transition])

    -- Code generation
    sem eval =
    | Reset clocks -> JsonArray (map (lam c. JsonString c) clocks)
    | Sync action -> JsonString action
    | TwoClockGuard (x, y, cmp, n) ->
        concat (concat (concat x (concat "-" y)) (cmp2string cmp)) (int2string n)
    | OneClockGuard (x, cmp, n) ->
        concat x (concat (cmp2string cmp) (int2string n))
    | GuardConjunct either ->
        match either with Left oneClockGuard then eval oneClockGuard else
        match either with Right twoClockGuard then eval twoClockGuard else
        error "Malformed Either"
    | Guard conjuncts -> JsonString (strJoin "&" (map eval conjuncts))
    -- TODO: Perhaps conjuncts would be better represented as elements in a JSON
    --       array. Will see later when doing code generation from JSON.
    | Properties (og, os, or) -> [
        ("guard", match og with Some g then eval g else JsonNull ()),
        ("sync", match os with Some s then eval s else JsonNull ()),
        ("reset", match or with Some r then eval r else JsonNull ())]
    | Transition (a, b, props) ->
        JsonObject (concat [
            ("from", JsonString a),
            ("to", JsonString b)] (eval props))
    | InvariantConjunct (x, cmp, n) ->
        concat x (concat (cmp2string cmp) (int2string n))
    | Invariant conjuncts -> JsonString (strJoin "&" (map eval conjuncts))
    | State (id, initial, invariant) ->
        JsonObject [
            ("id", JsonString id),
            ("initial", JsonBool initial),
            ("invariant", match invariant with Some inv then eval inv else JsonNull ())]
    | Program (states, transitions) ->
        JsonObject [
            ("states", JsonArray (map (lam s. eval s) states)),
            ("transitions", JsonArray (map (lam t. eval t) transitions))]

    -- Semantic checks
    sem check =
    | Program (states, transitions) ->
        let iss = filter (lam s.
            match s with State (_, initial, _) then
                initial
            else error "Malformed State") states in
        if neqi (length iss) 1 then
            Some (concat "Semantic error: " (concat (int2string (length iss)) " initial states"))
        else None ()
end

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

utest showError (testParser identifier "guard")
with "Parse error at 1:1: Unexpected keyword 'guard'. Expected identifier"

utest testParser identifier "foo" with
Success ("foo", ("", {file="", row=1, col=4}))

-- Parsers ---------------------------------------------------------------------

mexpr use TA in

let lt: Parser Cmp = bind (symbol "<") (lam _. pure (Lt ())) in
let ltEq: Parser Cmp = bind (symbol "<=") (lam _. pure (LtEq ())) in
let eq: Parser Cmp = bind (symbol "==") (lam _. pure (Eq ())) in
let gtEq: Parser Cmp = bind (symbol ">=") (lam _. pure (GtEq ())) in
let gt: Parser Cmp = bind (symbol ">") (lam _. pure (Gt ())) in

let cmp: Parser Cmp = alt eq (alt ltEq (alt lt (alt gtEq gt))) in
let cmpInvar: Parser Cmp = alt ltEq lt in

let reset: Parser Expression =
    bind (string "reset") (lam _.
    bind (symbol "{") (lam _.
    bind identifier (lam c.
    bind (many (apr (symbol ",") identifier)) (lam cs.
    bind (symbol "}") (lam _.
    pure (Reset (cons c cs))))))) in

let sync: Parser Expression =
    bind (string "sync") (lam _.
    bind (symbol "{") (lam _.
    bind identifier (lam a.
    bind (symbol "}") (lam _.
    pure (Sync a))))) in

let twoClockGuard: Parser Expression =
    bind identifier (lam a.
    bind (symbol "-") (lam _.
    bind identifier (lam b.
    bind cmp (lam c.
    bind number (lam n.
    pure (TwoClockGuard (a, b, c, n))))))) in

let oneClockGuard: Parser Expression =
    bind identifier (lam a.
    bind cmp (lam c.
    bind number (lam n.
    pure (OneClockGuard (a, c, n))))) in

let guardConjunct: Parser Expression =
    bind (alt (try oneClockGuard) twoClockGuard) (lam expr.
    match expr with OneClockGuard _ then pure (GuardConjunct (Left expr))
    else pure (GuardConjunct (Right expr))) in

let guard: Parser Expression =
    bind (string "guard") (lam _.
    bind (symbol "{") (lam _.
    bind (sepBy (symbol "&") guardConjunct) (lam cs.
    if eqi (length cs) 0 then fail "}" "clock constraint" else
    bind (symbol "}") (lam _.
    pure (Guard cs))))) in

let properties: Parser Expression =
    bind (optional guard) (lam og.
    bind (optional sync) (lam os.
    bind (optional reset) (lam or.
    pure (Properties (og, os, or))))) in

let transition: Parser Expression =
    bind identifier (lam a.
    bind (symbol "->") (lam _.
    bind identifier (lam b.
    bind properties (lam props.
    pure (Transition (a, b, props)))))) in

let invariantConjunct: Parser Expression =
    bind identifier (lam id.
    bind cmpInvar (lam c.
    bind number (lam n.
    pure (InvariantConjunct (id, c, n))))) in

let invariant: Parser Expression =
    bind (string "invar") (lam _.
    bind (symbol "{") (lam _.
    bind (sepBy (symbol "&") invariantConjunct) (lam cs.
    if eqi (length cs) 0 then fail "}" "clock constraint" else
    bind (symbol "}") (lam _.
    pure (Invariant cs))))) in

let state: Parser Expression =
    bind (optional (string "init")) (lam init.
    bind identifier (lam id.
    bind (notFollowedBy (symbol "->")) (lam _.
    bind (optional invariant) (lam invar.
    pure (State (id, match init with Some _ then true else false, invar)))))) in

let program: Parser Expression =
    bind (many (alt (try state) transition)) (lam ls.
    let ss = filter (lam x. match x with State _ then true else false) ls in
    let ts = filter (lam x. match x with Transition _ then true else false) ls in
    pure (Program (ss, ts))) in

-- Tests -----------------------------------------------------------------------

utest testParser cmpInvar "<" with
Success (Lt (), ("", {file="", row=1, col=2})) in

utest testParser cmpInvar "<=" with
Success (LtEq (), ("", {file="", row=1, col=3})) in

utest testParser cmp "<" with
Success (Lt (), ("", {file="", row=1, col=2})) in

utest testParser cmp "<=" with
Success (LtEq (), ("", {file="", row=1, col=3})) in

-- TODO: How is e.g. `<=>` handled? Should be parse error?
-- It is now LtEq, with rest ">".

utest testParser cmp "==" with
Success (Eq (), ("", {file="", row=1, col=3})) in

utest testParser cmp ">=" with
Success (GtEq (), ("", {file="", row=1, col=3})) in

utest testParser cmp ">" with
Success (Gt (), ("", {file="", row=1, col=2})) in

utest testParser invariant "invar { x < 10 }" with
Success (Invariant ([InvariantConjunct ("x", Lt (), 10)]),("", {file = "", row=1, col=17})) in

utest eval (Invariant [InvariantConjunct ("x", Lt (), 10)]) with
JsonString ("x<10") in

utest testParser state "bar invar { x < 10 }" with
Success (State ("bar", false, Some (Invariant [InvariantConjunct ("x", Lt (), 10)])), ("", {file="", row=1, col=21})) in

utest eval (State ("bar", false, Some (Invariant [InvariantConjunct ("x", Lt (), 10)]))) with
JsonObject [
    ("id", JsonString "bar"),
    ("initial", JsonBool false),
    ("invariant", JsonString "x<10")] in

utest testParser state "init foo" with
Success (State ("foo", true, None ()), ("", {file="", row=1, col=9})) in

utest testParser reset "reset { }" with
Failure (("'}'"),("valid identifier"),(("}"),{file = ([]),row = 1,col = 9})) in

utest testParser reset "reset { foo }" with
Success (TA_Reset ([("foo")]),(([]),{file = ([]),row = 1,col = 14})) in

utest testParser reset "reset { foo bar }" with
Failure (("'b'"),("'}'"),(("bar }"),{file = ([]),row = 1,col = 13})) in

utest testParser reset "reset { foo, bar }" with
Success (TA_Reset ([("foo"),("bar")]),(([]),{file = ([]),row = 1,col = 19})) in

utest testParser reset "reset { foo, bar, baz }" with
Success (TA_Reset ([("foo"),("bar"),("baz")]),(([]),{file = ([]),row = 1,col = 24})) in

-- Main ------------------------------------------------------------------------

if eqi (length argv) 1 then () else

let quiet = if eqString (get argv 1) "--quiet" then true else false in
let write = if eqString (get argv 1) "--write" then true else false in
let tests = (splitAt argv (if or quiet write then 2 else 1)).1 in

let compareAndPrint = lam t. lam output.
    let refFile = concat (splitAt t (subi (length t) 3)).0 ".out" in
    let refExists = fileExists refFile in

    -- Write new reference output
    let _ = if write then writeFile refFile output else () in

    let res = if write then "new -"
        else if not refExists then "? ---"
        else if eqString output (readFile refFile) then "pass "
        else "fail " in

    let _ = printLn (concat "-- Test " (concat t (concat ": " (concat res "---------------------------------------------------------------")))) in
    let _ = if quiet then () else print output in
    ()
in

let pj = pyimport "json" in

let _ = map (lam t.
    -- Parsing
    let parseResult = testParser program (readFile t) in
    let syncheck = match parseResult with Failure _ then Some (showError parseResult) else None () in

    match syncheck with Some s then
        compareAndPrint t (concat s "\n")
    else
        let ast = match parseResult with Success (x, _) then x
            else error "This should already be caught by `syncheck` above" in

        -- Semantic checks
        let semcheck = check ast in

        -- Code generation
        let json = formatJson (eval ast) in

        -- Json formatting
        let jsonPy = pycall pj "loads" (json,) in
        let jsonPyPretty = pycallkw pj "dumps" (jsonPy,) { indent=4, sort_keys="True" } in
        let jsonPretty = pyconvert jsonPyPretty in

        -- Compare with expected output
        let output = concat (concat (match semcheck with Some s then concat s "\n" else "") jsonPretty) "\n" in
        compareAndPrint t output
) tests in

()
