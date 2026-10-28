import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_finiteDimensional_adjoin_jqNModC
attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single

open ModularCurve
theorem ModularCurve.finiteDimensional_adjoin_jqNModC (K : Type*) [Field K] {N : ℕ} [NeZero N] (data : ModularPolynomialData N) : FiniteDimensional (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) (IntermediateField.adjoin (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) ({jqNModC K N} : Set (LaurentSeries K))) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_finiteDimensional_adjoin_jqNModC.solution
