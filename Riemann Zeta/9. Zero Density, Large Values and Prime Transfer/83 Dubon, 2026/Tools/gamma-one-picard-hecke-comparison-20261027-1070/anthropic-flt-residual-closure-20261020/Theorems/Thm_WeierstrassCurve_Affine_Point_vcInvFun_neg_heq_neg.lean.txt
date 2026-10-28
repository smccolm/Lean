import Mathlib
import Definitions.Def_ModularCurve_ModuliPoint
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_Point_vcInvFun_neg_heq_neg

open WeierstrassCurve WeierstrassCurve.Affine
theorem WeierstrassCurve.Affine.Point.vcInvFun_neg_heq_neg {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve F) (P : W.toAffine.Point) :
    HEq (Point.vcInvFun (⟨-1, 0, -W.a₁, -W.a₃⟩ : VariableChange F) W.toAffine P) (-P) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_Point_vcInvFun_neg_heq_neg.solution
