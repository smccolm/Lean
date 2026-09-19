import Expdb.Basic.AutomaticUniformity
import Expdb.Basic.PowerAsymptotics
import Expdb.ExponentialSums.ExponentSumGrowthNonAsymptotic

/-!
# ANTEDB asymptotic compatibility bridge

This bootstrap module imports the pinned ANTEDB definitions and proofs under
the project's Lean 4.30 dependency graph. It intentionally introduces no new
mathematical declaration. Source-facing bridge theorems belong here only when
their exact semantics and dependency edges are proved.
-/
