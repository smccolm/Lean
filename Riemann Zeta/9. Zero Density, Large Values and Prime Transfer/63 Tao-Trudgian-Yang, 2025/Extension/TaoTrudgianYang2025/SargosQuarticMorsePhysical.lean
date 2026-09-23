import TaoTrudgianYang2025.SargosQuarticMorseInverse

/-! Exact normalization of the original quartic phase at its actual stationary point. -/

noncomputable section

open Set

namespace TaoTrudgianYang2025

theorem sargosQuarticPhase_normalize {N α : ℝ}
    (hN : N ≠ 0) (hα : α ≠ 0) (γ x : ℝ) :
    α*N^2*sargosQuarticPhase 1 (γ*N^2/α) (x/N) = sargosQuarticPhase α γ x := by
  unfold sargosQuarticPhase
  field_simp

theorem sargosQuarticSlope_normalize {N α : ℝ}
    (hN : N ≠ 0) (hα : α ≠ 0) (γ x : ℝ) :
    α*N*sargosQuarticSlope 1 (γ*N^2/α) (x/N) = sargosQuarticSlope α γ x := by
  unfold sargosQuarticSlope
  field_simp

theorem sargosQuartic_normalized_coefficient_bound {N α γ : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2)) :
    |γ*N^2/α| ≤ 1/96 := by
  rw [abs_div,abs_mul,abs_pow,abs_of_pos hN,abs_of_pos hα]
  calc
    _ ≤ (α/(96*N^2))*N^2/α := by gcongr
    _ = _ := by field_simp

theorem sargosQuartic_normalized_inverse_mem {N α γ y : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (hy : y ∈ sargosQuarticSlopeRange N α γ) :
    sargosQuarticInverseSlope N α γ y/N ∈ Ioo 1 2 := by
  have hx := sargosQuarticInverseSlope_mem hN hα hγ hy
  constructor
  · exact (lt_div_iff₀ hN).mpr (by simpa only [one_mul] using hx.1)
  · exact (div_lt_iff₀ hN).mpr hx.2

theorem sargosQuartic_normalized_stationary_slope {N α γ y : ℝ}
    (hN : N ≠ 0) (hα : α ≠ 0) (hy : y ∈ sargosQuarticSlopeRange N α γ) :
    sargosQuarticSlope 1 (γ*N^2/α) (sargosQuarticInverseSlope N α γ y/N) = y/(α*N) := by
  apply (eq_div_iff (mul_ne_zero hα hN)).mpr
  rw [mul_comm,sargosQuarticSlope_normalize hN hα,sargosQuarticSlope_inverse hy]

theorem sargosQuartic_physical_quadratic_normalForm {N α γ y x : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (hy : y ∈ sargosQuarticSlopeRange N α γ) (hx : x ∈ Icc N (2*N)) :
    sargosQuarticPhase α γ x-y*x =
      sargosQuarticLegendre N α γ y+
        (α*N^2/2)*(sargosQuarticMorseCoordinate (γ*N^2/α)
          (sargosQuarticInverseSlope N α γ y/N) (x/N))^2 := by
  have he := sargosQuartic_normalized_coefficient_bound hN hα hγ
  have hr := sargosQuartic_normalized_inverse_mem hN hα hγ hy
  have hrc : sargosQuarticInverseSlope N α γ y/N ∈ Icc 0 3 := by
    constructor <;> linarith [hr.1,hr.2]
  have hxc : x/N ∈ Icc 0 3 := by
    have hl : 1 ≤ x/N := (le_div_iff₀ hN).mpr (by simpa only [one_mul] using hx.1)
    have hu : x/N ≤ 2 := (div_le_iff₀ hN).mpr hx.2
    constructor <;> linarith
  have hp := (sargosQuarticMorseCoefficient_bounds he hrc hxc).1
  have hform := sargosQuarticMorseCoordinate_normalForm (by linarith : 0 ≤
    sargosQuarticMorseCoefficient (γ*N^2/α) (sargosQuarticInverseSlope N α γ y/N) (x/N))
  have hscaled := congrArg (fun t : ℝ => α*N^2*t) hform
  dsimp only at hscaled
  rw [mul_sub,mul_sub,sargosQuarticPhase_normalize hN.ne' hα.ne',
    sargosQuarticPhase_normalize hN.ne' hα.ne'] at hscaled
  rw [sargosQuartic_normalized_stationary_slope hN.ne' hα.ne' hy] at hscaled
  have hslope : α*N^2*(y/(α*N)*(x/N-sargosQuarticInverseSlope N α γ y/N)) =
      y*(x-sargosQuarticInverseSlope N α γ y) := by
    field_simp
  rw [hslope] at hscaled
  unfold sargosQuarticLegendre
  nlinarith only [hscaled]

theorem sargosQuartic_physical_stationary_amplitude {N α γ y : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (hy : y ∈ sargosQuarticSlopeRange N α γ) :
    (N/Real.sqrt (α*N^2))*
        deriv (sargosQuarticMorseInverse (γ*N^2/α)
          (sargosQuarticInverseSlope N α γ y/N)) 0 =
      1/Real.sqrt (2*α+12*γ*(sargosQuarticInverseSlope N α γ y)^2) := by
  have he := sargosQuartic_normalized_coefficient_bound hN hα hγ
  have hr := sargosQuartic_normalized_inverse_mem hN hα hγ hy
  have hro : sargosQuarticInverseSlope N α γ y/N ∈ Ioo 0 3 := by
    constructor <;> linarith [hr.1,hr.2]
  have hc : 2*α+12*γ*(sargosQuarticInverseSlope N α γ y)^2 =
      α*(2+12*(γ*N^2/α)*(sargosQuarticInverseSlope N α γ y/N)^2) := by
    field_simp
  have hT : Real.sqrt (α*N^2) = Real.sqrt α*N := by
    rw [Real.sqrt_mul hα.le,Real.sqrt_sq_eq_abs,abs_of_pos hN]
  rw [sargosQuarticMorseInverse_deriv_zero he hro,hc,hT,Real.sqrt_mul hα.le]
  rw [show N/(Real.sqrt α*N) = (Real.sqrt α)⁻¹ by field_simp]
  simp only [one_div,mul_inv_rev]
  ring


end TaoTrudgianYang2025
