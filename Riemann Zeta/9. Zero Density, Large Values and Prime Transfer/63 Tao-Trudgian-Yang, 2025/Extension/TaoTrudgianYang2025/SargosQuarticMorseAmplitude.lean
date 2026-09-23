import TaoTrudgianYang2025.SargosQuarticMorseChangeVariables

/-! Actual transported cutoff and Jacobian, including the critical-point cutoff value. -/

noncomputable section

open Set
open scoped ContDiff

namespace TaoTrudgianYang2025

def sargosQuarticMorseAmplitude (χ : ℝ → ℝ) (ε r z : ℝ) : ℝ :=
  χ (sargosQuarticMorseInverse ε r z)*deriv (sargosQuarticMorseInverse ε r) z

theorem sargosQuarticMorseAmplitude_contDiffAt {χ : ℝ → ℝ} {ε r z : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3)
    (hz : z ∈ sargosQuarticMorseRange ε r) :
    ContDiffAt ℝ ∞ (sargosQuarticMorseAmplitude χ ε r) z := by
  have hi := sargosQuarticMorseInverse_contDiffAt hε hr hz
  exact (hχ.contDiffAt.comp z hi).mul (hi.derivWithin (by simp))

theorem sargosQuarticMorseAmplitude_zero {χ : ℝ → ℝ} {ε r : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Ioo 0 3) :
    sargosQuarticMorseAmplitude χ ε r 0 = χ r*(Real.sqrt (2+12*ε*r^2))⁻¹ := by
  rw [sargosQuarticMorseAmplitude,sargosQuarticMorseInverse_zero hε ⟨hr.1.le,hr.2.le⟩,
    sargosQuarticMorseInverse_deriv_zero hε hr]

theorem sargosQuarticMorseAmplitude_abs_le {χ : ℝ → ℝ} {ε r z M : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3)
    (hz : z ∈ sargosQuarticMorseRange ε r)
    (hM : 0 ≤ M) (hχ : ∀ u ∈ Ioo (0 : ℝ) 3, |χ u| ≤ M) :
    |sargosQuarticMorseAmplitude χ ε r z| ≤ M*(16/7) := by
  rw [sargosQuarticMorseAmplitude,abs_mul,
    abs_of_pos (sargosQuarticMorseInverse_deriv_pos hε hr hz)]
  exact mul_le_mul (hχ _ (sargosQuarticMorseInverse_mem hε hr hz))
    (sargosQuarticMorseInverse_deriv_bounds hε hr hz).2
    (sargosQuarticMorseInverse_deriv_pos hε hr hz).le hM

theorem sargosQuarticMorseAmplitude_nonneg {χ : ℝ → ℝ} {ε r z : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3)
    (hz : z ∈ sargosQuarticMorseRange ε r)
    (hχ : ∀ u ∈ Ioo (0 : ℝ) 3, 0 ≤ χ u) :
    0 ≤ sargosQuarticMorseAmplitude χ ε r z :=
  mul_nonneg (hχ _ (sargosQuarticMorseInverse_mem hε hr hz))
    (sargosQuarticMorseInverse_deriv_pos hε hr hz).le

end TaoTrudgianYang2025

