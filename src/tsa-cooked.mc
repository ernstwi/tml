include "either.mc"
include "json.mc"
include "tsa-base.mc"

lang TsaCooked = TsaBase
    syn Expression =
    | Program {
        locations: [Location],
        edges: [Edge]
    }

    sem cmp2string =
    | Lt () -> "<"
    | LtEq () -> "<="
    | Eq () -> "=="
    | GtEq () -> ">="
    | Gt () -> ">"

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
    -- (todo): Perhaps conjuncts would be better represented as elements in a JSON
    --         array. Will see later when doing code generation from JSON.
    | Edge (a, b, og, os, or) ->
        JsonObject [
            ("from", JsonString a),
            ("to", JsonString b),
            ("guard", match og with Some g then eval g else JsonNull ()),
            ("sync", match os with Some s then eval s else JsonNull ()),
            ("reset", match or with Some r then eval r else JsonNull ())]
    | InvariantConjunct (x, cmp, n) ->
        concat x (concat (cmp2string cmp) (int2string n))
    | Invariant conjuncts -> JsonString (strJoin "&" (map eval conjuncts))
    | Location (id, initial, invariant) ->
        JsonObject [
            ("id", JsonString id),
            ("initial", JsonBool initial),
            ("invariant", match invariant with Some inv then eval inv else JsonNull ())]
    | Program (locations, edges) ->
        JsonObject [
            ("locations", JsonArray (map (lam l. eval l) locations)),
            ("edges", JsonArray (map (lam e. eval e) edges))]
end
