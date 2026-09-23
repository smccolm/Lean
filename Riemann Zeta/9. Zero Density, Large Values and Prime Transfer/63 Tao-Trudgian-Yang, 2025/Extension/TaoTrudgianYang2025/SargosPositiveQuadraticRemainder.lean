import TaoTrudgianYang2025.BetaQuadraticLocalRemainder

/-! Positive-curvature Fresnel remainders obtained by exact complex conjugation. -/

noncomputable section

open Set MeasureTheory
open scoped ContDiff FourierTransform ComplexConjugate

namespace TaoTrudgianYang2025

theorem sargos_fourier_conj (t : ℝ) :
    conj (𝐞 (-t) : ℂ) = (𝐞 t : ℂ) := by
  rw [AddChar.map_neg_eq_inv,Circle.coe_inv_eq_conj]
  simp

theorem sargos_positive_quadratic_conj (T z : ℝ) :
    conj (betaQuadraticKernel T z) = (𝐞 ((T/2)*z^2) : ℂ) := by
  rw [betaQuadraticKernel,neg_mul,sargos_fourier_conj]

theorem sargos_positive_quadratic_global_remainder {W : ℝ → ℝ} {T H M₀ M₂ M₃ : ℝ}
    (hW : ContDiff ℝ ∞ W) (hT : 0 < T) (hH : 0 < H)
    (hs : Function.support W ⊆ Ioc (-H) H) (h₀ : |W 0| ≤ M₀)
    (h₂ : ∀ z : ℝ, |iteratedDeriv 2 W z| ≤ M₂)
    (h₃ : ∀ z : ℝ, |iteratedDeriv 3 W z| ≤ M₃) :
    ‖(∫ z : ℝ, (W z : ℂ)*(𝐞 ((T/2)*z^2) : ℂ))-
      (W 0 : ℂ)*((𝐞 ((1 : ℝ)/8) : ℂ)/(Real.sqrt T : ℂ))‖ ≤
        quadraticRemainderConstant H M₀ M₂ M₃/T := by
  have he :
      (∫ z : ℝ, (W z : ℂ)*(𝐞 ((T/2)*z^2) : ℂ))-
        (W 0 : ℂ)*((𝐞 ((1 : ℝ)/8) : ℂ)/(Real.sqrt T : ℂ)) =
      conj ((∫ z : ℝ, (W z : ℂ)*betaQuadraticKernel T z)-
        (W 0 : ℂ)*((𝐞 (-(1 : ℝ)/8) : ℂ)/(Real.sqrt T : ℂ))) := by
    rw [map_sub,← integral_conj]
    simp only [map_mul,map_div₀,Complex.conj_ofReal,sargos_positive_quadratic_conj,
      neg_div,sargos_fourier_conj]
  rw [he,Complex.norm_conj]
  exact norm_quadratic_global_remainder_le hW hT hH hs h₀ h₂ h₃

end TaoTrudgianYang2025
