include "base.mc"
include "internal-action.mc"

-- Language containing every "shallow" feature of TML (= features that can be
-- compiled to the base TSA model).

lang TSA = Base + InternalAction

mexpr
use TSA in
utest checkProgram [Location ("foo", true, []), Edge ("foo", "bar", [Sync (InternalAction "baz")])] with ["Invalid InternalAction id: baz"] in
utest checkProgram [Location ("foo", true, []), Edge ("foo", "bar", [Sync (InternalAction "az")])] with [] in
()
