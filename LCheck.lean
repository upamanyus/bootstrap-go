/- The Lean-native checkers' library root, with no program logic (see
LCheck/Syntax.lean), precompiled to native code (lakefile.toml):

* `lcheck`, the CSL checker of checker/ (LCheck/{Syntax,Fns,Check}.lean);
* `ltcheck`, the table-driven checker of tcheck/ (LCheck/TCheck/). -/
import LCheck.Check
import LCheck.TCheck.Check
