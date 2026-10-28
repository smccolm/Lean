import Mathlib
import Definitions.Def_WeierstrassCurve_VeluQuotientMap
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_isOddVeluSet_oddOrderSummingSet

open WeierstrassCurve WeierstrassCurve.Affine
theorem WeierstrassCurve.isOddVeluSet_oddOrderSummingSet
    {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F}
    {Q : W.toAffine.Point} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hord : addOrderOf Q = p) {n : ℕ} (hn : n ≤ (p - 1) / 2) :
    W.IsOddVeluSet (W.oddOrderSummingSet Q n) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_isOddVeluSet_oddOrderSummingSet.solution
