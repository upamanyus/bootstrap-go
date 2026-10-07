/- The library root: everything `lake build` checks. -/
import Checkers.GooseLang.HeapAdequacy
import Checkers.Checker.Prelude
import Checkers.Checker.Soundness
import Checkers.Checker.Adequacy
import Checkers.Checker.Examples.Double
import Checkers.Checker.Examples.Max
import Checkers.Checker.Examples.Swap
import Checkers.Checker.Examples.Abs
import Checkers.Checker.Examples.CondStore
import Checkers.Checker.Examples.Median3
import Checkers.Checker.Examples.Observed.Median3
import Checkers.TCheck.Raft.Proof.raft__becomeFollower
