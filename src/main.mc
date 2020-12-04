include "base.mc"
include "token.mc"

-- Argument parsing ------------------------------------------------------------

mexpr

if eqi (length argv) 1 then () else
let quiet = if eqString (get argv 1) "--quiet" then true else false in
let write = if eqString (get argv 1) "--write" then true else false in
let offset = (if or quiet write then 2 else 1) in
let tests = (splitAt argv offset).1 in

-- Main ------------------------------------------------------------------------

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

    let prefix = concat "-- Test " (concat t (concat ": " res)) in
    let _ = printLn (concat prefix (makeSeq (subi 80 (length prefix)) '-')) in
    let _ = if quiet then () else print outputNL in
    ()
in

let pj = pyimport "json" in

use SOURCE_LANG in
map (lam t.
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

        -- Code generation
        let json = formatJson (jsonModel (evalProgram cooked)) in

        -- Json formatting
        let jsonPy = pycall pj "loads" (json,) in
        let jsonPyPretty = pycallkw pj "dumps" (jsonPy,)
            { indent=4, sort_keys="True" } in
        let jsonPretty = pyconvert jsonPyPretty in

        -- Compare with expected output
        compareAndPrint t jsonPretty
) tests
