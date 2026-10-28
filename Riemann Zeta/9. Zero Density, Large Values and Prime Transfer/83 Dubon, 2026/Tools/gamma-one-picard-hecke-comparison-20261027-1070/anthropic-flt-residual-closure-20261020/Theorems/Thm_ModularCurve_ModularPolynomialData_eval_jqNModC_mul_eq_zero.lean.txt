import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_ModularPolynomialData_eval_jqNModC_mul_eq_zero
attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single

theorem ModularCurve.ModularPolynomialData.eval_jqNModC_mul_eq_zero {ℓ : ℕ} [NeZero ℓ] (data : ModularCurve.ModularPolynomialData ℓ) (K : Type*) [CommRing K] (d : ℕ) [NeZero d] : data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (ModularCurve.jqNModC K d)).toRingHom (ModularCurve.jqNModC K (d * ℓ)) = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ModularPolynomialData_eval_jqNModC_mul_eq_zero.solution
