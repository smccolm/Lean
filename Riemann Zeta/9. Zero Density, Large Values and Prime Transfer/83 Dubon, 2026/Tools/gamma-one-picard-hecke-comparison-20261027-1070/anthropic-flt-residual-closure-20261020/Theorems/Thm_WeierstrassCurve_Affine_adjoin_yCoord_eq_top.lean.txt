import Mathlib
import Definitions.Def_WeierstrassCurve_FunctionFieldQuadratic
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_adjoin_yCoord_eq_top

theorem WeierstrassCurve.Affine.adjoin_yCoord_eq_top {F : Type*} [Field F] {W : WeierstrassCurve.Affine F} :
    IntermediateField.adjoin (RatFunc F) {WeierstrassCurve.Affine.yCoord W} = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_adjoin_yCoord_eq_top.solution
