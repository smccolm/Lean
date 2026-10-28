import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_isIntegral_jqNModC_of_modularPolynomialData

open ModularCurve
theorem ModularCurve.isIntegral_jqNModC_of_modularPolynomialData (K : Type*) [Field K] {N : ℕ} [NeZero N] (data : ModularPolynomialData N) :
    IsIntegral (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) (jqNModC K N) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isIntegral_jqNModC_of_modularPolynomialData.solution
