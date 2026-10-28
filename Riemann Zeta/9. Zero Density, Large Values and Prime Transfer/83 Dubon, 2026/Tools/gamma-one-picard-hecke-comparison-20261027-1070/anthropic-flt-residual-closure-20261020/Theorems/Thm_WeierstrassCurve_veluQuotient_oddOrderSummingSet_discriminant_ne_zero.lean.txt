import Mathlib
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_ne_zero
attribute [-simp] WeierstrassCurve.veluX_empty WeierstrassCurve.veluY_empty

open WeierstrassCurve
theorem WeierstrassCurve.veluQuotient_oddOrderSummingSet_discriminant_ne_zero
    {L : Type*} [Field L] [DecidableEq L] [IsAlgClosed L] (h2 : (2 : L) ≠ 0)
    (W : WeierstrassCurve L) [W.IsElliptic] (n : ℕ) (Q : W.toAffine.Point)
    (hQ : addOrderOf Q = 2 * n + 1) :
    (W.veluQuotient (W.oddOrderSummingSet Q n)).Δ ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_ne_zero.solution
