import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_analyticOrderAt_le_of_isIntegral_adjoin_coeffEmb_jq
attribute [-instance] WeierstrassCurve.Affine.Point.instFinite
attribute [-simp] ModularCurve.jqNModC_one

open ModularCurve
theorem ModularCurve.analyticOrderAt_le_of_isIntegral_adjoin_coeffEmb_jq (N : ℕ) {k : ℤ}
    (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k) (X : LaurentSeries ℂ)
    (hX : X * ((UpperHalfPlane.qExpansion 1 (h : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) = ((UpperHalfPlane.qExpansion 1 (g : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ))
    (h₁ : IsIntegral (Algebra.adjoin ℂ ({ModularCurve.coeffEmb ℂ ModularCurve.jq} : Set (LaurentSeries ℂ)))
      (X ^ 6 * ModularCurve.coeffEmb ℂ ModularCurve.jq ^ 4 * (ModularCurve.coeffEmb ℂ ModularCurve.jq - algebraMap ℂ (LaurentSeries ℂ) 1728) ^ 3))
    (τ : UpperHalfPlane) :
    analyticOrderAt ((fun z : UpperHalfPlane => h z * ModularForm.discriminant z) ∘ UpperHalfPlane.ofComplex) (τ : ℂ) ≤
      analyticOrderAt ((fun z : UpperHalfPlane => g z * ModularForm.E₄ z ^ 2 * ModularForm.E₆ z) ∘ UpperHalfPlane.ofComplex) (τ : ℂ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_analyticOrderAt_le_of_isIntegral_adjoin_coeffEmb_jq.solution
