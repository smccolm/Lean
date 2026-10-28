import Mathlib
import Definitions.Def_WeierstrassCurve_FunctionFieldQuadratic
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_finiteDimensional_ratFunc_functionField

theorem WeierstrassCurve.Affine.finiteDimensional_ratFunc_functionField {F : Type*} [Field F] (W : WeierstrassCurve.Affine F) :
    FiniteDimensional (RatFunc F) W.FunctionField := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_finiteDimensional_ratFunc_functionField.solution
