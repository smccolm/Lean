import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_finrank_adjoin_jqNModC_le
attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single

open ModularCurve
theorem ModularCurve.finrank_adjoin_jqNModC_le (K : Type*) [Field K] {N : ℕ} [NeZero N] (data : ModularPolynomialData N) : Module.finrank (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) (IntermediateField.adjoin (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) ({jqNModC K N} : Set (LaurentSeries K))) ≤ dedekindPsi N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_finrank_adjoin_jqNModC_le.solution
