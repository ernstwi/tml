include "base.mc"
include "internal-action.mc"
include "sync-action.mc"
include "token.mc"

-- Language fragment compositions ----------------------------------------------

-- TSA containins every "shallow" feature of TML (= features that can be
-- compiled to the base TSA model).
lang TSA = Base + InternalAction

-- TSA with input/output actions.
lang TsaSyncAction = TSA + SyncAction

-- Equivalent to above at the moment.
lang All = Base + InternalAction + SyncAction

-- Helper functions ------------------------------------------------------------

-- Parse one or more occurrences of `p` separated by single occurrences of `sep`.
let sepBy1: Parser s -> Parser a -> Parser [a] =
    lam sep. lam p.
    bind p (lam hd.
    bind (many (apr sep p)) (lam tl.
    pure (cons hd tl)))

-- Argument parsing ------------------------------------------------------------

mexpr

if eqi (length argv) 1 then () else
let quiet = if eqString (get argv 1) "--quiet" then true else false in
let write = if eqString (get argv 1) "--write" then true else false in
let offset = (if or quiet write then 2 else 1) in
let sourceLang = get argv offset in
let tests = (splitAt argv (addi offset 1)).1 in

-- InternalAction parsers ------------------------------------------------------

use InternalAction in

let internalAction: Parser Action =
    bind identifier (lam id.
    pure (InternalAction id)) in

-- SyncAction parsers ----------------------------------------------------------

use SyncAction in

let syncAction: Parser Action =
    bind identifier (lam id.
    alt (apr (symbol "?") (pure (InputAction id)))
        (apr (symbol "!") (pure (OutputAction id)))) in

-- TsaSyncAction parsers -------------------------------------------------------

use TsaSyncAction in

let tsaSyncAction: Parser Action = alt (try syncAction) internalAction in

-- Plumbing --------------------------------------------------------------------

let action: Parser Action =
    match sourceLang with "tsa" then internalAction else
    match sourceLang with "tsa+sync" then tsaSyncAction else
    never in

-- Base parsers ----------------------------------------------------------------

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

let invariant: Parser PropertyModifier =
    bind (string "invar") (lam _.
    alt
    (bind (symbol "!") (lam _. pure (Left (ClearInvariant ()))))
    (bind (symbol "{") (lam _.
    bind (sepBy1 (symbol "&") invariantConjunct) (lam cs.
    bind (symbol "}") (lam _.
    pure (Right (Invariant cs))))))) in


let guard: Parser PropertyModifier =
    bind (string "guard") (lam _.
    alt
    (bind (symbol "!") (lam _. pure (Left (ClearGuard ()))))
    (bind (symbol "{") (lam _.
    bind (sepBy1 (symbol "&") guardConjunct) (lam cs.
    bind (symbol "}") (lam _.
    pure (Right (Guard cs))))))) in

let sync: Parser PropertyModifier =
    bind (string "sync") (lam _.
    alt
    (bind (symbol "!") (lam _. pure (Left (ClearSync ()))))
    (bind (symbol "{") (lam _.
    bind action (lam a.
    bind (symbol "}") (lam _.
    pure (Right (Sync a))))))) in

let reset: Parser PropertyModifier =
    bind (string "reset") (lam _.
    alt
    (bind (symbol "!") (lam _. pure (Left (ClearReset ()))))
    (bind (symbol "{") (lam _.
    bind (sepBy1 (symbol ",") identifier) (lam cs.
    bind (symbol "}") (lam _.
    pure (Right (Reset cs))))))) in

--------------------------------------------------------------------------------

let property: Parser PropertyModifier =
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
    bind (label "anything but ->" (notFollowedBy (symbol "->"))) (lam _.
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

let locationOrEdge: Parser StatementRaw =
    lam st.
    let res = location st in
    match res with Failure (_, "anything but ->", _) then
        edge st
    else res in

--------------------------------------------------------------------------------

let statement: Parser StatementRaw = alt default locationOrEdge in

--------------------------------------------------------------------------------

let program: Parser ProgramRaw =
    bind (many1 statement) (lam ss.
    bind (alt (apl (string "\n") endOfInput) endOfInput) (lam _.
    pure ss)) in

-- Main ------------------------------------------------------------------------

use All in
-- (todo): Avoid this shortcut? With this setup, we get cases from all
-- fragments, e.g:
--
-- syn Action =
-- | InternalAction String
-- | InputAction String
-- | OutputAction String
--
-- sem jsonAction =
-- | InternalAction id ->
--     JsonObject [ ("type", JsonString "internal"), ("id", JsonString id) ]
-- | InputAction id ->
--     JsonObject [ ("type", JsonString "input"), ("id", JsonString id) ]
-- | OutputAction id ->
--     JsonObject [ ("type", JsonString "output"), ("id", JsonString id) ]
-- | _ -> never
--
-- The negatives are
-- 1. If we have by error e.g. created an InputAction while using TSA language,
--    this will not be caught by jsonAction.
-- 2. We can't have two language fragments which define different cases using
--    the same name.

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
            compareAndPrint t
                (strJoin "\n" (map (lam e. concat "Semantic error: " e) semcheck))
        else

        let cooked = cookProgram raw in
        -- let _ = dprint cooked in

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
