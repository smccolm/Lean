import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_laurentBaseChange_modularFunctionField

theorem ModularCurve.laurentBaseChange_modularFunctionField (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N] : ModularCurve.laurentBaseChange L (ModularCurve.modularFunctionField N) = ModularCurve.modularFunctionFieldC L N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_laurentBaseChange_modularFunctionField.solution
