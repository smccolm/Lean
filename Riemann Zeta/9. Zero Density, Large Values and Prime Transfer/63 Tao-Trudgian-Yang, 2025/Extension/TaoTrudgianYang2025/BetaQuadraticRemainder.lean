import TaoTrudgianYang2025.BetaQuadraticTaylor

/-!
# A quantitative whole-line quadratic stationary remainder

Taylor's exact integral remainder, odd cancellation, integration by parts,
and the proved finite Fresnel error give an explicit O(1/T) estimate.
-/

noncomputable section

open Set Expdb MeasureTheory
open scoped ContDiff FourierTransform

namespace TaoTrudgianYang2025

def quadraticRemainderConstant (H M₀ M₂ M₃ : ℝ) : ℝ :=
  4*M₀/(H*Real.pi)+(2*H*M₂+2*H*(M₂+H*M₃))/(2*Real.pi)

theorem quadraticRemainderConstant_nonneg {H M₀ M₂ M₃ : ℝ}
    (hH : 0 < H) (h₀ : 0 ≤ M₀) (h₂ : 0 ≤ M₂) (h₃ : 0 ≤ M₃) :
    0 ≤ quadraticRemainderConstant H M₀ M₂ M₃ := by
  unfold quadraticRemainderConstant
  positivity

theorem norm_quadratic_window_remainder_le
    {W : ℝ → ℝ} {T H M₀ M₂ M₃ : ℝ}
    (hW : ContDiff ℝ ∞ W) (hT : 0 < T) (hH : 0 < H)
    (h₀ : |W 0| ≤ M₀)
    (h₂ : ∀ z : ℝ, |iteratedDeriv 2 W z| ≤ M₂)
    (h₃ : ∀ z : ℝ, |iteratedDeriv 3 W z| ≤ M₃) :
    ‖(∫ z in (-H)..H, (W z : ℂ)*betaQuadraticKernel T z)-
      (W 0 : ℂ)*((𝐞 (-(1 : ℝ)/8) : ℂ)/(Real.sqrt T : ℂ))‖ ≤
        quadraticRemainderConstant H M₀ M₂ M₃/T := by
  have hparts := norm_integral_sq_mul_betaQuadraticKernel_le
    (quadraticTaylorCoefficient_contDiff hW) hT hH
    (abs_quadraticTaylorCoefficient_le h₂)
    (abs_deriv_quadraticTaylorCoefficient_le hW h₃)
  have htail := norm_betaQuadraticWindow_sub_main hT hH
  rw [integral_weighted_betaQuadraticKernel_taylor hW]
  have he :
      (W 0 : ℂ)*(∫ z in (-H)..H, betaQuadraticKernel T z)+
          (∫ z in (-H)..H, ((z^2*quadraticTaylorCoefficient W z : ℝ) : ℂ)*
            betaQuadraticKernel T z)-
          (W 0 : ℂ)*((𝐞 (-(1 : ℝ)/8) : ℂ)/(Real.sqrt T : ℂ)) =
      (W 0 : ℂ)*((∫ z in (-H)..H, betaQuadraticKernel T z)-
          (𝐞 (-(1 : ℝ)/8) : ℂ)/(Real.sqrt T : ℂ))+
          ∫ z in (-H)..H, ((z^2*quadraticTaylorCoefficient W z : ℝ) : ℂ)*
            betaQuadraticKernel T z := by ring
  rw [he]
  apply (norm_add_le _ _).trans
  have hmain :
      ‖(W 0 : ℂ)*((∫ z in (-H)..H, betaQuadraticKernel T z)-
        (𝐞 (-(1 : ℝ)/8) : ℂ)/(Real.sqrt T : ℂ))‖ ≤ M₀*(4/(T*H*Real.pi)) := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul h₀ htail (norm_nonneg _) ((abs_nonneg _).trans h₀)
  apply (add_le_add hmain hparts).trans_eq
  unfold quadraticRemainderConstant
  field_simp

theorem norm_quadratic_global_remainder_le
    {W : ℝ → ℝ} {T H M₀ M₂ M₃ : ℝ}
    (hW : ContDiff ℝ ∞ W) (hT : 0 < T) (hH : 0 < H)
    (hs : Function.support W ⊆ Ioc (-H) H)
    (h₀ : |W 0| ≤ M₀)
    (h₂ : ∀ z : ℝ, |iteratedDeriv 2 W z| ≤ M₂)
    (h₃ : ∀ z : ℝ, |iteratedDeriv 3 W z| ≤ M₃) :
    ‖(∫ z : ℝ, (W z : ℂ)*betaQuadraticKernel T z)-
      (W 0 : ℂ)*((𝐞 (-(1 : ℝ)/8) : ℂ)/(Real.sqrt T : ℂ))‖ ≤
        quadraticRemainderConstant H M₀ M₂ M₃/T := by
  have hs' : Function.support (fun z : ℝ => (W z : ℂ)*betaQuadraticKernel T z) ⊆ Ioc (-H) H := by
    intro z hz
    apply hs
    intro hzero
    exact hz (by simp only [hzero,Complex.ofReal_zero,zero_mul])
  rw [← intervalIntegral.integral_eq_integral_of_support_subset hs']
  exact norm_quadratic_window_remainder_le hW hT hH h₀ h₂ h₃

end TaoTrudgianYang2025
