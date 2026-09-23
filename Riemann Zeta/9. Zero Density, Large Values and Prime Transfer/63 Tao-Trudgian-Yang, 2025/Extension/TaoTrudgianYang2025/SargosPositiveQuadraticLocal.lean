import TaoTrudgianYang2025.SargosPositiveQuadraticRemainder

/-! Positive-curvature Fresnel remainders with local derivative budgets only. -/

noncomputable section

open Set MeasureTheory
open scoped ContDiff FourierTransform ComplexConjugate

namespace TaoTrudgianYang2025

theorem sargos_positive_quadratic_window_remainder {W : ℝ → ℝ} {T H M₀ M₂ M₃ : ℝ}
    (hW : ContDiff ℝ ∞ W) (hT : 0 < T) (hH : 0 < H)
    (h₀ : |W 0| ≤ M₀)
    (h₂ : ∀ z ∈ Icc (-H) H, |iteratedDeriv 2 W z| ≤ M₂)
    (h₃ : ∀ z ∈ Icc (-H) H, |iteratedDeriv 3 W z| ≤ M₃) :
    ‖(∫ z in (-H)..H, (W z : ℂ)*(𝐞 ((T/2)*z^2) : ℂ))-
      (W 0 : ℂ)*((𝐞 ((1:ℝ)/8) : ℂ)/(Real.sqrt T : ℂ))‖ ≤
        quadraticRemainderConstant H M₀ M₂ M₃/T := by
  have he :
      (∫ z in (-H)..H, (W z : ℂ)*(𝐞 ((T/2)*z^2) : ℂ))-
        (W 0 : ℂ)*((𝐞 ((1:ℝ)/8) : ℂ)/(Real.sqrt T : ℂ)) =
      conj ((∫ z in (-H)..H, (W z : ℂ)*betaQuadraticKernel T z)-
        (W 0 : ℂ)*((𝐞 (-(1:ℝ)/8) : ℂ)/(Real.sqrt T : ℂ))) := by
    simp only [intervalIntegral.integral_of_le (show -H ≤ H by linarith)]
    rw [map_sub,← integral_conj]
    simp only [map_mul,map_div₀,Complex.conj_ofReal,sargos_positive_quadratic_conj,
      neg_div,sargos_fourier_conj]
  rw [he,Complex.norm_conj]
  exact norm_quadratic_window_remainder_le_local hW hT hH h₀ h₂ h₃

end TaoTrudgianYang2025

