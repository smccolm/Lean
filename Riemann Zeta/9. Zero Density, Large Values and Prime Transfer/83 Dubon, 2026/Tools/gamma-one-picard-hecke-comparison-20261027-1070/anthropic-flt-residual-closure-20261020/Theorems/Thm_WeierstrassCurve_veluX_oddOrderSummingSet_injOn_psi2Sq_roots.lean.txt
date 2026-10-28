import Mathlib
import Definitions.Def_WeierstrassCurve_VeluQuotientMap
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_veluX_oddOrderSummingSet_injOn_psi2Sq_roots

open WeierstrassCurve
theorem WeierstrassCurve.veluX_oddOrderSummingSet_injOn_psi2Sq_roots
    {L : Type*} [Field L] [DecidableEq L] (h2 : (2 : L) ≠ 0)
    (W : WeierstrassCurve L) [W.IsElliptic] (n : ℕ) (Q : W.toAffine.Point)
    (hQ : addOrderOf Q = 2 * n + 1) {r r' : L}
    (hr : W.Ψ₂Sq.eval r = 0) (hr' : W.Ψ₂Sq.eval r' = 0)
    (heq : W.veluX (W.oddOrderSummingSet Q n) r = W.veluX (W.oddOrderSummingSet Q n) r') :
    r = r' := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_veluX_oddOrderSummingSet_injOn_psi2Sq_roots.solution
