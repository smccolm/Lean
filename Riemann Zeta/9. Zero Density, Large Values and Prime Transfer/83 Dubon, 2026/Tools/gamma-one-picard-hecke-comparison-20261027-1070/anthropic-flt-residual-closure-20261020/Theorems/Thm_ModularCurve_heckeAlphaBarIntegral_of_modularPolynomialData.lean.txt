import Definitions.Def_ModularCurve_HeckeOperator
import P2M.Util
import P2M.Sol.S_ModularCurve_heckeAlphaBarIntegral_of_modularPolynomialData
attribute [-simp] ModularCurve.jqNModC_one

theorem ModularCurve.heckeAlphaBarIntegral_of_modularPolynomialData (L : Type*) [Field L] [Algebra ℚ L] {ℓ : ℕ} [NeZero ℓ] (data : ModularCurve.ModularPolynomialData ℓ) (hℓ : ℓ.Prime) (N : ℕ) [NeZero N] : ModularCurve.HeckeAlphaBarIntegral L N ℓ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_heckeAlphaBarIntegral_of_modularPolynomialData.solution
