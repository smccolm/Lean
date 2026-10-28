import Mathlib
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_Point_vcInvFun_add

theorem WeierstrassCurve.Affine.Point.vcInvFun_add {K : Type*} [Field K] [DecidableEq K]
    (C : WeierstrassCurve.VariableChange K) (W : WeierstrassCurve.Affine K) (P Q : W.Point) :
    WeierstrassCurve.Affine.Point.vcInvFun C W (P + Q) =
      WeierstrassCurve.Affine.Point.vcInvFun C W P + WeierstrassCurve.Affine.Point.vcInvFun C W Q := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_Point_vcInvFun_add.solution
