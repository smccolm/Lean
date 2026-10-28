import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_laurentBaseChange_mono

theorem ModularCurve.laurentBaseChange_mono (L : Type*) [Field L] [Algebra ℚ L] {F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)} (h : F₀ ≤ F₁) : ModularCurve.laurentBaseChange L F₀ ≤ ModularCurve.laurentBaseChange L F₁ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_laurentBaseChange_mono.solution
