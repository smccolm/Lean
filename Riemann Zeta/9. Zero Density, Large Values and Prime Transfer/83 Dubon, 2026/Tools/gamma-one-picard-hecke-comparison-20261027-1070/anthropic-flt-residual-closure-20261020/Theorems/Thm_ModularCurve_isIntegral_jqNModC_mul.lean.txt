import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_isIntegral_jqNModC_mul
attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single

theorem ModularCurve.isIntegral_jqNModC_mul {K : Type*} [Field K] (F : IntermediateField K (LaurentSeries K)) {ℓ : ℕ} [NeZero ℓ] (data : ModularCurve.ModularPolynomialData ℓ) (d : ℕ) [NeZero d] (hd : ModularCurve.jqNModC K d ∈ F) : IsIntegral F (ModularCurve.jqNModC K (d * ℓ)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_isIntegral_jqNModC_mul.solution
