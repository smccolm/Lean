import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_laurentBaseChange_modularFunctionFieldFull

theorem ModularCurve.laurentBaseChange_modularFunctionFieldFull (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N] : ModularCurve.laurentBaseChange L (ModularCurve.modularFunctionFieldFull N) = IntermediateField.adjoin L {x | ∃ (d : ℕ) (_ : NeZero d), d ∣ N ∧ x = ModularCurve.jqNModC L d} := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_laurentBaseChange_modularFunctionFieldFull.solution
