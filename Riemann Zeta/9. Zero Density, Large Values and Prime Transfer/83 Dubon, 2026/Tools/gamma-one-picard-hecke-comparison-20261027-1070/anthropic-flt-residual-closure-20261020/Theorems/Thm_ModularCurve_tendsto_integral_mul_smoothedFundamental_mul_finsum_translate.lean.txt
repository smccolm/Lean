import Mathlib
import Definitions.Def_ModularCurve_SmoothedFundamental
import P2M.Util
import P2M.Sol.S_ModularCurve_tendsto_integral_mul_smoothedFundamental_mul_finsum_translate
attribute [-instance] FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions

open UpperHalfPlane MeasureTheory Filter
open scoped MatrixGroups Topology ComplexConjugate

theorem ModularCurve.tendsto_integral_mul_smoothedFundamental_mul_finsum_translate
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (F : ℂ → ℂ) (hF : Continuous F) (hFs : HasCompactSupport F)
    (hFU : tsupport F ⊆ {z : ℂ | 0 < z.im})
    (g : ℍ → ℂ) (hg : Continuous g)
    (hgw : ∀ γ ∈ Γ, ∀ τ : ℍ, g (γ • τ) = denom (γ : GL (Fin 2) ℝ) τ ^ 2 * g τ)
    (h : ℝ → ℂ → ℂ) (hh : ∀ T z, h T z = (ModularCurve.smoothedFundamental Γ T z : ℂ)) :
    (∀ T : ℝ, Integrable fun z : ℂ => g (ofComplex z) * h T z *
        ∑ᶠ γ : Γ, F (((γ : SL(2, ℤ)) • ofComplex z : ℍ) : ℂ) *
          conj (1 / denom ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) (ofComplex z) ^ 2)) ∧
    Tendsto (fun T : ℝ => ∫ z : ℂ, g (ofComplex z) * h T z *
        ∑ᶠ γ : Γ, F (((γ : SL(2, ℤ)) • ofComplex z : ℍ) : ℂ) *
          conj (1 / denom ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) (ofComplex z) ^ 2)) atTop
      (𝓝 (∫ z : ℂ, g (ofComplex z) * F z)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_tendsto_integral_mul_smoothedFundamental_mul_finsum_translate.solution
