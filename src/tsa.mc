include "base.mc"
include "internal-action.mc"

-- Language containing every "shallow" feature of TML (= features that can be
-- compiled to the base TSA model).

lang TSA = Base + InternalAction

mexpr use TSA in

utest checkProgram [
    LocationStmtRaw {
        id = "foo",
        initial = true,
        properties = []
    }, EdgeStmtRaw {
        from = "foo",
        to = "bar",
        properties = [Sync (InternalAction "az")]
    }
] with [] in

()
