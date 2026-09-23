import TaoTrudgianYang2025.SargosQuarticSourceExpansion
import TaoTrudgianYang2025.SargosQuarticLegendreScale

/-! The actual stationary-scale cutoff and its source-range plateau. -/

noncomputable section

open Set

namespace TaoTrudgianYang2025

def sargosQuarticStationaryWidth (N α : ℝ) : ℝ := (Real.sqrt (α*N^2))⁻¹

theorem sargosQuarticStationaryWidth_eq {N α : ℝ} (hN : 0 < N) (hα : 0 < α) :
    sargosQuarticStationaryWidth N α = 1/(N*Real.sqrt α) := by
  rw [sargosQuarticStationaryWidth,Real.sqrt_mul hα.le,Real.sqrt_sq_eq_abs,abs_of_pos hN]
  ring

theorem sargosQuarticStationaryWidth_inverse_sq {N α : ℝ} (hα : 0 ≤ α) :
    (sargosQuarticStationaryWidth N α)⁻¹^2 = α*N^2 := by
  rw [sargosQuarticStationaryWidth,inv_inv,Real.sq_sqrt (by positivity)]

theorem sargosQuarticStationaryWidth_source {N : ℕ} {α : ℝ}
    (hN : 9216 ≤ N) (hα : 1/Real.sqrt (N : ℝ) ≤ α) :
    0 < sargosQuarticStationaryWidth N α ∧
      sargosQuarticStationaryWidth N α ≤ 1 ∧
      ((N : ℝ)+1)/N+4*sargosQuarticStationaryWidth N α < 2 := by
  have hNr : (9216:ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0:ℝ) < N := by linarith
  have ha := sargosQuartic_source_scale hNr hα
  have hT : 0 < α*(N : ℝ)^2 := by positivity [ha.1]
  have hT64 : 64 ≤ α*(N : ℝ)^2 := by
    have hh := mul_le_mul ha.2.1 (show (1:ℝ) ≤ N by linarith)
      (by norm_num : (0:ℝ) ≤ 1) (mul_pos ha.1 hNp).le
    nlinarith
  have hs : 8 ≤ Real.sqrt (α*(N : ℝ)^2) := by
    nlinarith [Real.sq_sqrt hT.le,Real.sqrt_nonneg (α*(N : ℝ)^2)]
  have he : sargosQuarticStationaryWidth N α ≤ 1/8 := by
    simpa only [sargosQuarticStationaryWidth,one_div] using
      one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 8) hs
  have hn : 1/(N : ℝ) ≤ 1/8 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hl : ((N : ℝ)+1)/N = 1+1/(N : ℝ) := by field_simp
  refine ⟨by unfold sargosQuarticStationaryWidth; positivity,by linarith,?_⟩
  rw [hl]
  linarith

theorem sargosQuarticStationaryWidth_smoothing {N α : ℝ}
    (hN : 0 < N) (hα : 0 < α) :
    4*N*sargosQuarticStationaryWidth N α = 4/Real.sqrt α := by
  rw [sargosQuarticStationaryWidth_eq hN hα]
  field_simp

theorem sargosQuarticStationaryWidth_transition {N α : ℝ}
    (hN : 0 < N) (hα : 0 < α) (E : ℝ) :
    (5*α*N*sargosQuarticStationaryWidth N α+6)*E/Real.sqrt α =
      5*E+6*E/Real.sqrt α := by
  rw [sargosQuarticStationaryWidth_eq hN hα]
  have hs : Real.sqrt α ≠ 0 := (Real.sqrt_pos.mpr hα).ne'
  have he := Real.sq_sqrt hα.le
  field_simp
  linear_combination -5*E*he

end TaoTrudgianYang2025
