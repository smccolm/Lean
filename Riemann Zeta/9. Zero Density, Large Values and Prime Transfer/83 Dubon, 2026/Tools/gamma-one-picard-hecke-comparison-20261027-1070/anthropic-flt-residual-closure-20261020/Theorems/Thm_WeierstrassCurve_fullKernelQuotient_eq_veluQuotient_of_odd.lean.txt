import Definitions.Def_WeierstrassCurve_FullKernelQuotient
import Definitions.Def_ModularCurve_CycSubRootBridgeOdd
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_fullKernelQuotient_eq_veluQuotient_of_odd

open scoped Classical
theorem WeierstrassCurve.fullKernelQuotient_eq_veluQuotient_of_odd {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
    (Q : W.toAffine.Point) {N : ℕ} (hN : Odd N) (hQ : addOrderOf Q = N) :
    W.fullKernelQuotient Q N = W.veluQuotient (W.oddOrderSummingSet Q ((N - 1) / 2)) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_fullKernelQuotient_eq_veluQuotient_of_odd.solution
