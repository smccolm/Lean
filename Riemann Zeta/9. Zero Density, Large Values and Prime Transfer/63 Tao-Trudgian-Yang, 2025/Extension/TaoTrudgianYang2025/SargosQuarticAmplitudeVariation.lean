import TaoTrudgianYang2025.SargosQuarticAmplitude
import TaoTrudgianYang2025.BetaAmplitudeVariation

/-! Finite variation of the actual quartic curvature weight on its genuine samples. -/

noncomputable section

open Set
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem finiteVariationBound_sargosQuarticStationaryAmplitude
    {N α γ : ℝ} (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (a : ℝ) (L : ℕ)
    (hr : ∀ i : ℕ, i ≤ L → a+i ∈
      Icc (sargosQuarticSlope α γ N) (sargosQuarticSlope α γ (2*N))) :
    FiniteVariationBound (fun i => (sargosQuarticStationaryAmplitude N α γ (a+i) : ℂ))
      L (1/Real.sqrt α) := by
  have hb : ∀ i : ℕ, i ≤ L → 0 ≤ sargosQuarticStationaryAmplitude N α γ (a+i) ∧
      sargosQuarticStationaryAmplitude N α γ (a+i) ≤ 1/Real.sqrt α := by
    intro i hi
    have h := sargosQuarticStationaryAmplitude_pos_bound hN hα hγ (hr i hi)
    exact ⟨h.1.le,h.2⟩
  rcases sargosQuarticStationaryAmplitude_monotone_or_antitone hN hα hγ with hm | hm
  · apply finiteVariationBound_of_monotone (by positivity) _ hb
    intro i hi j hj hij
    exact hm (hr i hi) (hr j hj)
      (add_le_add le_rfl (show (i : ℝ) ≤ (j : ℝ) by exact_mod_cast hij))
  · apply finiteVariationBound_of_antitone (by positivity) _ hb
    intro i hi j hj hij
    exact hm (hr i hi) (hr j hj)
      (add_le_add le_rfl (show (i : ℝ) ≤ (j : ℝ) by exact_mod_cast hij))

theorem sargosQuarticStationaryAmplitude_sum_le_prefix_bound
    {N α γ : ℝ} (hN : 0 < N) (hα : 0 < α) (hγ : |γ| ≤ α/(96*N^2))
    (a : ℝ) (L : ℕ)
    (hr : ∀ i : ℕ, i ≤ L → a+i ∈
      Icc (sargosQuarticSlope α γ N) (sargosQuarticSlope α γ (2*N)))
    (z : ℕ → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hz : ∀ j ≤ L+1, ‖∑ i ∈ Finset.range j, z i‖ ≤ B) :
    ‖∑ i ∈ Finset.range (L+1), (sargosQuarticStationaryAmplitude N α γ (a+i) : ℂ)*z i‖ ≤
      (2/Real.sqrt α)*B := by
  have h := norm_sum_range_succ_mul_le_of_finiteVariation
    (finiteVariationBound_sargosQuarticStationaryAmplitude hN hα hγ a L hr) hB hz
  convert h using 1
  ring

end TaoTrudgianYang2025
