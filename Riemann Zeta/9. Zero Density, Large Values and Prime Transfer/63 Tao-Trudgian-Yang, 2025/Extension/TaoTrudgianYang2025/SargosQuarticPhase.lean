import TaoTrudgianYang2025.SargosQuarticCurvature
import TaoTrudgianYang2025.SargosQuarticSource
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! The actual quartic phase, its slope, and uniform curvature on the source interval. -/

noncomputable section

open Set GafniTao
open scoped ContDiff BigOperators

namespace TaoTrudgianYang2025

def sargosQuarticPhase (α γ x : ℝ) : ℝ := α*x^2+γ*x^4

def sargosQuarticSlope (α γ x : ℝ) : ℝ := 2*α*x+4*γ*x^3

theorem sargosQuarticSum_eq_phase (N : ℕ) (z : ℤ → ℂ) (α γ : ℝ) :
    sargosQuarticSum N z α γ =
      ∑ n ∈ sargosSourceInterval N, z n*fordAdditiveCharacter (sargosQuarticPhase α γ n) := by
  rw [sargosQuarticSum_eq_source]
  rfl

theorem sargosQuarticPhase_hasDerivAt (α γ x : ℝ) :
    HasDerivAt (sargosQuarticPhase α γ) (sargosQuarticSlope α γ x) x := by
  change HasDerivAt (fun t : ℝ => α*t^2+γ*t^4) (2*α*x+4*γ*x^3) x
  convert (((hasDerivAt_id x).pow 2).const_mul α).add
    (((hasDerivAt_id x).pow 4).const_mul γ) using 1
  dsimp only [id_eq]
  ring

theorem sargosQuarticSlope_hasDerivAt (α γ x : ℝ) :
    HasDerivAt (sargosQuarticSlope α γ) (2*α+12*γ*x^2) x := by
  change HasDerivAt (fun t : ℝ => 2*α*t+4*γ*t^3) (2*α+12*γ*x^2) x
  convert ((hasDerivAt_id x).const_mul (2*α)).add
    (((hasDerivAt_id x).pow 3).const_mul (4*γ)) using 1
  dsimp only [id_eq]
  ring

theorem contDiff_sargosQuarticPhase (α γ : ℝ) :
    ContDiff ℝ ∞ (sargosQuarticPhase α γ) := by
  unfold sargosQuarticPhase
  fun_prop

theorem contDiff_sargosQuarticSlope (α γ : ℝ) :
    ContDiff ℝ ∞ (sargosQuarticSlope α γ) := by
  unfold sargosQuarticSlope
  fun_prop

theorem sargosQuartic_curvature_error {N α γ x : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2)) (hx : x ∈ Icc N (2*N)) :
    |12*γ*x^2| ≤ α/2 := by
  have hx0 : 0 ≤ x := hN.le.trans hx.1
  have hxsq : x^2 ≤ (2*N)^2 := pow_le_pow_left₀ hx0 hx.2 2
  rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 12),abs_pow,
    abs_of_nonneg hx0]
  calc
    _ ≤ 12*(α/(96*N^2))*(2*N)^2 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hγ (by norm_num)) hxsq
        (sq_nonneg x) (by positivity)
    _ = _ := by field_simp; ring

theorem sargosQuarticPhase_curvature {N α γ x : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2)) (hx : x ∈ Icc N (2*N)) :
    3*α/2 ≤ 2*α+12*γ*x^2 ∧ 2*α+12*γ*x^2 ≤ 5*α/2 := by
  have h := abs_le.mp (sargosQuartic_curvature_error hN hα hγ hx)
  constructor <;> linarith [h.1,h.2]

theorem sargosQuarticSlope_strictMonoOn {N α γ : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2)) :
    StrictMonoOn (sargosQuarticSlope α γ) (Icc N (2*N)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc N (2*N))
    (contDiff_sargosQuarticSlope α γ).continuous.continuousOn
  intro x hx
  rw [(sargosQuarticSlope_hasDerivAt α γ x).deriv]
  exact lt_of_lt_of_le (by positivity : 0 < 3*α/2)
    (sargosQuarticPhase_curvature hN hα hγ (interior_subset hx)).1

theorem sargosQuartic_ratio_bound {N α γ x : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2)) (hx : x ∈ Icc N (2*N)) :
    |2*γ*x^2/α| ≤ 1/12 := by
  have hx0 : 0 ≤ x := hN.le.trans hx.1
  have hxsq : x^2 ≤ (2*N)^2 := pow_le_pow_left₀ hx0 hx.2 2
  rw [abs_div,abs_mul,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2),abs_pow,
    abs_of_nonneg hx0,abs_of_pos hα]
  calc
    _ ≤ (2*(α/(96*N^2))*(2*N)^2)/α := by
      apply div_le_div_of_nonneg_right _ hα.le
      exact mul_le_mul (mul_le_mul_of_nonneg_left hγ (by norm_num)) hxsq
        (sq_nonneg x) (by positivity)
    _ = _ := by field_simp; ring

end TaoTrudgianYang2025
