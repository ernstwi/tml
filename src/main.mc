include "tml.mc"
include "token.mc"

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
-- transition ::= id "->" id prop*
-- prop       ::= "guard {" guards "}"
--              | "sync {" action "}"
--              | "reset {" clocks "}"
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
-- Semantic rules:
-- • Exactly one initial state
-- • At most one of each property per transition (guard, sync, reset)

-- Parsers ---------------------------------------------------------------------

mexpr use TML in

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
    bind (many (alt guard (alt sync reset))) (lam ps.
    pure (Properties ps)) in

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

-- Unit tests ------------------------------------------------------------------

utest testParser cmpInvar "<" with
Success (Lt (), ("", {file="", row=1, col=2})) in

utest testParser cmpInvar "<=" with
Success (LtEq (), ("", {file="", row=1, col=3})) in

utest testParser cmp "<" with
Success (Lt (), ("", {file="", row=1, col=2})) in

utest testParser cmp "<=" with
Success (LtEq (), ("", {file="", row=1, col=3})) in

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
Success (TmlAst_Reset ([("foo")]),(([]),{file = ([]),row = 1,col = 14})) in

utest testParser reset "reset { foo bar }" with
Failure (("'b'"),("'}'"),(("bar }"),{file = ([]),row = 1,col = 13})) in

utest testParser reset "reset { foo, bar }" with
Success (TmlAst_Reset ([("foo"),("bar")]),(([]),{file = ([]),row = 1,col = 19})) in

utest testParser reset "reset { foo, bar, baz }" with
Success (TmlAst_Reset ([("foo"),("bar"),("baz")]),(([]),{file = ([]),row = 1,col = 24})) in

-- Main ------------------------------------------------------------------------

if eqi (length argv) 1 then () else

let quiet = if eqString (get argv 1) "--quiet" then true else false in
let write = if eqString (get argv 1) "--write" then true else false in
let tests = (splitAt argv (if or quiet write then 2 else 1)).1 in

let compareAndPrint = lam t. lam output.
    let outputNL = concat output "\n" in
    let refFile = concat (splitAt t (subi (length t) 3)).0 ".out" in
    let refExists = fileExists refFile in

    -- Write new reference output
    let _ = if write then writeFile refFile outputNL else () in

    let res = if write then "new -"
        else if not refExists then "? ---"
        else if eqString outputNL (readFile refFile) then "pass "
        else "fail " in

    let _ = printLn (concat "-- Test " (concat t (concat ": " (concat res "---------------------------------------------------------------")))) in
    let _ = if quiet then () else print outputNL in
    ()
in

let pj = pyimport "json" in

let _ = map (lam t.
    -- Parsing
    let parseResult = testParser program (readFile t) in
    let syncheck = match parseResult with Failure _ then Some (showError parseResult) else None () in

    match syncheck with Some s then
        compareAndPrint t s
    else
        let ast = match parseResult with Success (x, _) then x
            else error "This should already be caught by `syncheck` above" in

        -- Semantic checks
        let semcheck = check ast in
        if gti (length semcheck) 0 then
            compareAndPrint t (strJoin "\n" semcheck)
        else

        -- AST transformation
        let astt = transform ast in

        -- Code generation
        let json = formatJson (eval astt) in

        -- Json formatting
        let jsonPy = pycall pj "loads" (json,) in
        let jsonPyPretty = pycallkw pj "dumps" (jsonPy,) { indent=4, sort_keys="True" } in
        let jsonPretty = pyconvert jsonPyPretty in

        -- Compare with expected output
        compareAndPrint t jsonPretty
) tests in

()
