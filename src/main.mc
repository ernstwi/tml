include "base.mc"
include "token.mc"

let pj = pyimport "json"

mexpr use SOURCE_LANG in

if eqi (length argv) 1 then () else
let t = head (tail argv) in

let parseResult = runParser t program (readFile t) in

match parseResult with Failure _ then
    print (showError parseResult)
else
    -- Parsing
    let raw = match parseResult with Success (x, _) then x else never in

    -- Semantic analysis
    let semcheck = checkProgram raw in
    if gti (length semcheck) 0 then
        print (strJoin "\n" (map (lam e. concat "Semantic error: " e) semcheck))
    else

    -- AST transformation
    let cooked = cookProgram raw in

    -- Code generation
    let json = formatJson (jsonModel (evalProgram cooked)) in

    -- Json formatting
    let jsonPy = pycall pj "loads" (json,) in
    let jsonPyPretty = pycallkw pj "dumps" (jsonPy,)
        { indent=4, sort_keys="True" } in
    let jsonPretty = pyconvert jsonPyPretty in

    print jsonPretty
