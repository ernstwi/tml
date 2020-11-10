include "ast.mc"
include "eval.mc"
include "semcheck.mc"
include "transform.mc"

lang TML = TmlAst + TmlCheck + TmlTransform + TmlEval
