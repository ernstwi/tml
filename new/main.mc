include "tsa.mc"
include "token.mc"

mexpr

use TSA in

let action: Parser Action =
    bind identifier (lam id.
    pure (InternalAction id)) in

use Base in

--------------------------------------------------------------------------------

let lt:   Parser Cmp = bind (symbol "<")  (lam _. pure (Lt ())) in
let ltEq: Parser Cmp = bind (symbol "<=") (lam _. pure (LtEq ())) in
let eq:   Parser Cmp = bind (symbol "==") (lam _. pure (Eq ())) in
let gtEq: Parser Cmp = bind (symbol ">=") (lam _. pure (GtEq ())) in
let gt:   Parser Cmp = bind (symbol ">")  (lam _. pure (Gt ())) in

--------------------------------------------------------------------------------

let cmp: Parser Cmp =
    alt eq (alt ltEq (alt lt (alt gtEq gt))) in

let cmpInvar: Parser Cmp =
    alt ltEq lt in

--------------------------------------------------------------------------------

let oneClockGuard: Parser GuardConjunct =
    bind identifier (lam a.
    bind cmp (lam c.
    bind number (lam n.
    pure (OneClockGuard (a, c, n))))) in
    
let twoClockGuard: Parser GuardConjunct =
    bind identifier (lam a.
    bind (symbol "-") (lam _.
    bind identifier (lam b.
    bind cmp (lam c.
    bind number (lam n.
    pure (TwoClockGuard (a, b, c, n))))))) in

--------------------------------------------------------------------------------

let invariantConjunct: Parser InvariantConjunct =
    bind identifier (lam id.
    bind cmpInvar (lam c.
    bind number (lam n.
    pure (id, c, n)))) in

let guardConjunct: Parser GuardConjunct =
    alt (try oneClockGuard) twoClockGuard in

--------------------------------------------------------------------------------

let invariant: Parser Property =
    bind (string "invar") (lam _.
    bind (symbol "{") (lam _.
    bind (sepBy (symbol "&") invariantConjunct) (lam cs.
    bind (symbol "}") (lam _.
    pure (Invariant cs))))) in


let guard: Parser Property =
    bind (string "guard") (lam _.
    bind (symbol "{") (lam _.
    bind (sepBy (symbol "&") guardConjunct) (lam cs.
    bind (symbol "}") (lam _.
    pure (Guard cs))))) in

let sync: Parser Property =
    bind (string "sync") (lam _.
    bind (symbol "{") (lam _.
    bind action (lam a.
    bind (symbol "}") (lam _.
    pure (Sync a))))) in

let reset: Parser Property =
    bind (string "reset") (lam _.
    bind (symbol "{") (lam _.
    bind identifier (lam c.
    bind (many (apr (symbol ",") identifier)) (lam cs.
    bind (symbol "}") (lam _.
    pure (Reset (cons c cs))))))) in

--------------------------------------------------------------------------------

let property: Parser Property =
    alt invariant (alt guard (alt sync reset)) in

--------------------------------------------------------------------------------

let locationDefault: Parser StatementRaw =
    bind (string "location") (lam _.
    bind (many property) (lam ps.
    pure (LocationDefaultRaw ps))) in

let edgeDefault: Parser StatementRaw =
    bind (string "edge") (lam _.
    bind (many property) (lam ps.
    pure (EdgeDefaultRaw ps))) in

--------------------------------------------------------------------------------

let location: Parser StatementRaw =
    bind (optional (string "init")) (lam init.
    bind identifier (lam id.
    bind (notFollowedBy (symbol "->")) (lam _.
    bind (many property) (lam ps.
    pure (LocationStmtRaw {
        id = id,
        initial = match init with Some _ then true else false,
        properties = ps
    }))))) in

let edge: Parser StatementRaw =
    bind identifier (lam a.
    bind (symbol "->") (lam _.
    bind identifier (lam b.
    bind (many property) (lam ps.
    pure (EdgeStmtRaw {
        from = a,
        to = b,
        properties = ps
    }))))) in

let default: Parser StatementRaw =
    bind (string "default") (lam _.
    alt locationDefault edgeDefault) in

--------------------------------------------------------------------------------

let statement: Parser StatementRaw = alt (try location) (alt edge default) in

--------------------------------------------------------------------------------

let program: Parser ProgramRaw = many statement in

-- Main ------------------------------------------------------------------------

use TSA in

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

    let _ = printLn (concat "-- Test " (concat t (concat ": " (concat res
        "---------------------------------------------------------------")))) in
    let _ = if quiet then () else print outputNL in
    ()
in

let pj = pyimport "json" in

let _ = map (lam t.
    let parseResult = runParser t program (readFile t) in
    
    match parseResult with Failure _ then
        compareAndPrint t (showError parseResult)
    else
        let raw = match parseResult with Success (x, _) then x else never in

        let semcheck = checkProgram raw in
        if gti (length semcheck) 0 then
            compareAndPrint t (strJoin "\n" semcheck)
        else

        let cooked = cookProgram raw in

        -- Code generation
        let json = formatJson (jsonModel (evalProgram cooked)) in

        -- Json formatting
        let jsonPy = pycall pj "loads" (json,) in
        let jsonPyPretty = pycallkw pj "dumps" (jsonPy,)
            { indent=4, sort_keys="True" } in
        let jsonPretty = pyconvert jsonPyPretty in

        -- Compare with expected output
        compareAndPrint t jsonPretty
) tests in

()
