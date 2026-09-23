import TaoTrudgianYang2025.SargosQuarticPoisson
import TaoTrudgianYang2025.SargosQuarticMorseWeightBounds

/-! The original physical quartic Fourier integral in actual positive quadratic coordinates. -/

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology FourierTransform

namespace TaoTrudgianYang2025

theorem sargosQuarticFourierMode_eq_normalized
    (χ : ℝ → ℝ) {N : ℝ} (hN : 0 < N) (α γ y : ℝ) :
    sargosQuarticFourierMode χ N α γ y =
      (N : ℂ)*(∫ u : ℝ, (χ u : ℂ)*(𝐞 (sargosQuarticPhase α γ (N*u)-y*(N*u)) : ℂ)) := by
  have he : (fun x : ℝ => (χ (x/N) : ℂ)*
      (𝐞 (sargosQuarticPhase α γ (N*(x/N))-y*(N*(x/N))) : ℂ)) =
      (fun x : ℝ => (χ (x/N) : ℂ)*(𝐞 (sargosQuarticPhase α γ x-y*x) : ℂ)) := by
    funext x
    rw [mul_div_cancel₀ x hN.ne']
  unfold sargosQuarticFourierMode
  rw [← he,Measure.integral_comp_div
    (fun u : ℝ => (χ u : ℂ)*(𝐞 (sargosQuarticPhase α γ (N*u)-y*(N*u)) : ℂ)) N,
    abs_of_pos hN,Complex.real_smul]

theorem sargosQuarticFourierMode_eq_global_morse {χ : ℝ → ℝ} {N α γ y : ℝ}
    (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (hy : y ∈ sargosQuarticSlopeRange N α γ) :
    sargosQuarticFourierMode χ N α γ y =
      (N : ℂ)*(𝐞 (sargosQuarticLegendre N α γ y) : ℂ)*
        ∫ z : ℝ, (sargosQuarticMorseWeight χ (γ*N^2/α)
          (sargosQuarticInverseSlope N α γ y/N) z : ℂ)*(𝐞 ((α*N^2/2)*z^2) : ℂ) := by
  have he := sargosQuartic_normalized_coefficient_bound hN hα hγ
  have hr := sargosQuartic_normalized_inverse_mem hN hα hγ hy
  have hrc : sargosQuarticInverseSlope N α γ y/N ∈ Icc 0 3 := by
    constructor <;> linarith [hr.1,hr.2]
  have hs' : tsupport χ ⊆ Ioo (0 : ℝ) 3 := by
    intro u hu
    have h := hs hu
    constructor <;> linarith [h.1,h.2]
  rw [sargosQuarticFourierMode_eq_normalized χ hN α γ y,
    sargosQuartic_integral_eq_global_morse hs' he hrc]
  rw [mul_assoc]
  congr 1
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z ∈ sargosQuarticMorseRange (γ*N^2/α) (sargosQuarticInverseSlope N α γ y/N)
  · rw [sargosQuarticMorseWeight_eq hz,sargosQuarticMorseAmplitude]
    by_cases hc : χ (sargosQuarticMorseInverse (γ*N^2/α)
        (sargosQuarticInverseSlope N α γ y/N) z) = 0
    · simp only [hc,zero_mul,Complex.ofReal_zero,mul_zero]
    · have hu := hs (subset_tsupport χ hc)
      have hx : N*sargosQuarticMorseInverse (γ*N^2/α)
          (sargosQuarticInverseSlope N α γ y/N) z ∈ Icc N (2*N) := by
        constructor <;> nlinarith [hu.1,hu.2]
      have hform := sargosQuartic_physical_quadratic_normalForm hN hα hγ hy hx
      rw [mul_div_cancel_left₀ _ hN.ne',sargosQuarticMorseCoordinate_inverse hz] at hform
      rw [hform,AddChar.map_add_eq_mul,Circle.coe_mul]
      ring
  · simp only [sargosQuarticMorseWeight_zero_of_not_mem hz,Complex.ofReal_zero,zero_mul,mul_zero]

end TaoTrudgianYang2025
