include "tsa-base.mc"
include "tsa-raw.mc"
include "tsa-cooked.mc"
include "tsa.mc"
include "token.mc"

-- Language definition ---------------------------------------------------------

-- EBNF variant: https://www.w3.org/TR/REC-xml/#sec-notation
--
-- Program         ::= (location | edge | default)*
--
-- location        ::= "init"? id invar?
--
-- invar           ::= "invar {" invarExpr "}")?
-- invarExpr       ::= invarConjunct ("&" invarConjunct)*
-- invarConjunct   ::= id ("<=" | "<") nat
--
-- edge            ::= id "->" id (guard | sync | reset)*
--
-- guard           ::= "guard {" guardExpr "}"
-- guardExpr       ::= guardConjunct ("&" guardConjunct)*
-- guardConjunct   ::= (id op nat) | (id "-" id op nat)
-- op              ::= "<=" | "<" | "==" | ">" | ">="
--
-- sync            ::= "sync {" action "}"
-- action          ::= id /* To be extended for communication */
--
-- reset           ::= "reset {" clocks "}"
-- clocks          ::= id ("," id)*
--
-- default         ::= locationDefault | edgeDefault
-- locationDefault ::= "default" "location" invar
-- edgeDefault     ::= "default" "edge" (guard | sync | reset)*
--
-- id              ::= (letter | "_") (letter | "_" | digit)*
-- letter          ::= [a-zA-Z]
-- digit           ::= [0-9]
-- nat             ::= [1-9] digit*
--
-- Semantic rules:
-- • Exactly one initial location
-- • At most one of each property per edge/edge default (guard, sync, reset)
-- • No repeated states/edges/defaults

-- Helper types and functions --------------------------------------------------

type EdgePropertyError
con EdgePropertyError : (Int, String) -> EdgePropertyError

let edgePropertyErrorString = lam e.
    match e with EdgePropertyError (n, s) then
        concat (int2string n) (concat " " s)
    else error "Error: EdgePropertyErrorString"

con SemanticFailure : (String, State) -> ParseResult

let semFail = lam description. lam st.
  SemanticFailure (description, st)

let showError = lam f : ParseResult.
  match f with Failure (found, expected, st) then
    let pos = st.1 in
    concat (concat (concat "Parse error at " (showPos pos)) ": ")
    (concat (concat "Unexpected " found)
            (if gti (length expected) 0
             then concat ". Expected " expected
             else ""))
  else match f with SemanticFailure (description, _) then
    concat "Semantic error: " description
  else error "Tried to show something that is not a failure"

-- Parsers ---------------------------------------------------------------------

mexpr use TSA in

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

-- Edge property helper functions

let edgePropertiesExtract: [Expression] -> Either EdgePropertyError (Option Expression)
    = lam f. lam s. lam props.
        let res = filter f props in
        match (length res) with 0 then
            Right (None ())
        else match (length res) with 1 then
            Right (Some (head res))
        else
            Left (EdgePropertyError ((length res), s)) in

let edgePropertiesGuard: [Expression] -> Either EdgePropertyError (Option Guard)
    = lam props. edgePropertiesExtract
        (lam p. match p with Guard _ then true else false)
        "guards"
        props in

let edgePropertiesSync: [Expression] -> Either EdgePropertyError (Option Sync)
    = lam props. edgePropertiesExtract
        (lam p. match p with Sync _ then true else false)
        "syncs"
        props in

let edgePropertiesReset: [Expression] -> Either EdgePropertyError (Option Reset)
    = lam props. edgePropertiesExtract
        (lam p. match p with Reset _ then true else false)
        "resets"
        props in

-- [Guard | Sync | Reset] -> [Option Guard, Option Sync, Option Reset]
let edgePropertiesCooked: [Expression] -> Either EdgePropertyError [Expression] =
    lam props.
        let res = [
            edgePropertiesGuard props,
            edgePropertiesSync props,
            edgePropertiesReset props
        ] in
        match eitherLefts res with [] then
            Right (eitherRights res)
        else Left (head (eitherLefts res)) in
        -- (todo): Just returning the first error. This is ok.
---

let edgeProperties: Parser [Expression] =
    fmap edgePropertiesCooked (many (alt guard (alt sync reset))) in

let edge: Parser Expression =
    bind identifier (lam a.
    bind (symbol "->") (lam _.
    bind identifier (lam b.
    bind edgeProperties (lam props.
    eitherEither
        (lam e. semFail (edgePropertyErrorString e))
        (lam props. pure (Edge (a, b, get props 0, get props 1, get props 2)))
        props
    )))) in

utest testParser edge "foo -> bar guard { x < 5 }" with
Success (
    Edge ("foo", "bar",
        Some (Guard [GuardConjunct (Left (OneClockGuard ("x", Lt (), 5)))]),
        None (),
        None ()
    ), ("", {file="", row=1, col=27})) in

utest testParser edge "foo -> bar guard { x < 5 } guard { x < 5 }" with
SemanticFailure (("2 guards"),(([]),{file = ([]),row = 1,col = 43})) in
utest showError (testParser edge "foo -> bar guard { x < 5 } guard { x < 5 }") with
"Semantic error: 2 guards" in

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

let location: Parser Expression =
    bind (optional (string "init")) (lam init.
    bind identifier (lam id.
    bind (notFollowedBy (symbol "->")) (lam _.
    bind (optional invariant) (lam invar.
    pure (Location (id, match init with Some _ then true else false, invar)))))) in

let edgeDefault: Parser Expression =
    bind (string "edge") (lam _.
    bind edgeProperties (lam props.
    eitherEither
        (lam e. semFail (edgePropertyErrorString e))
        (lam props. pure (EdgeDefault (get props 0, get props 1, get props 2)))
        props
    )) in

let locationDefault: Parser Expression =
    bind (string "location") (lam _.
    bind invariant (lam invar.
    pure (LocationDefault (Some invar)))) in

let default: Parser Expression =
    bind (string "default") (lam _.
    alt locationDefault edgeDefault) in

-- Cook an array of possibly multiple Defaults to one set of properties
let defaultsCooked: [Default] -> Either EdgePropertyError [Expression] = lam ds.
    match length ds with 0 then
        Right []
    else match length ds with 1 then
        match head ds with LocationDefault oi then
            Right [oi]
        else match head ds with EdgeDefault (og, os, or) then
            Right [og, os, or]
        else never
    else
        Left (EdgePropertyError ((length ds), match head ds with LocationDefault _ then "location defaults" else "edge defaults")) in

let program: Parser Expression =
    bind (many (alt (try location) (alt edge default))) (lam xs.
    bind (alt endOfInput (bind (string "\n") (lam _. endOfInput))) (lam _.
    let ls = filter (lam x. match x with Location _ then true else false) xs in
    let es = filter (lam x. match x with Edge _ then true else false) xs in
    let lds = filter (lam x. match x with LocationDefault _ then true else false) xs in
    let eds = filter (lam x. match x with EdgeDefault _ then true else false) xs in

    let ldsCooked = defaultsCooked lds in
    let edsCooked = defaultsCooked eds in

    match ldsCooked with Left err then semFail (edgePropertyErrorString err)
    else match edsCooked with Left err then semFail (edgePropertyErrorString err)
    else pure (Program (ls, es,
        match defaultsCooked lds with Right [oi] then oi else None (),
        match defaultsCooked eds with Right [og, _, _] then og else None (),
        match defaultsCooked eds with Right [_, os, _] then os else None (),
        match defaultsCooked eds with Right [_, _, or] then or else None ())))) in

utest testParser program "default location invar { x < 5 }" with
Success (
    Program ([], [],
        Some (Invariant ([InvariantConjunct (("x"),Lt (),5)])),
        None (),None (),None ()
    ), ("", {file = ([]),row = 1,col = 33})) in

utest testParser program "default edge reset { x }" with
Success (Program (([]),([]),None (),None (),None (), Some (Reset ([("x")]))),(([]),{file = ([]),row = 1,col = 25})) in

utest showError (testParser program "default edge reset { x } reset { y }") with
"Semantic error: 2 resets" in

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

utest testParser location "bar invar { x < 10 }" with
Success (Location ("bar", false, Some (Invariant [InvariantConjunct ("x", Lt (), 10)])), ("", {file="", row=1, col=21})) in

utest eval (Location ("bar", false, Some (Invariant [InvariantConjunct ("x", Lt (), 10)]))) with
JsonObject [
    ("id", JsonString "bar"),
    ("initial", JsonBool false),
    ("invariant", JsonString "x<10")] in

utest testParser location "init foo" with
Success (Location ("foo", true, None ()), ("", {file="", row=1, col=9})) in

utest testParser reset "reset { }" with
Failure (("'}'"),("valid identifier"),(("}"),{file = ([]),row = 1,col = 9})) in

utest testParser reset "reset { foo }" with
Success (Reset ([("foo")]),(([]),{file = ([]),row = 1,col = 14})) in

utest testParser reset "reset { foo bar }" with
Failure (("'b'"),("'}'"),(("bar }"),{file = ([]),row = 1,col = 13})) in

utest testParser reset "reset { foo, bar }" with
Success (Reset ([("foo"),("bar")]),(([]),{file = ([]),row = 1,col = 19})) in

utest testParser reset "reset { foo, bar, baz }" with
Success (Reset ([("foo"),("bar"),("baz")]),(([]),{file = ([]),row = 1,col = 24})) in

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
    let syncheck = match parseResult with Failure _ | SemanticFailure _ then Some (showError parseResult) else None () in

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
