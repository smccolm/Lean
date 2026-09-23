import TaoTrudgianYang2025.BetaHalfDuality

/-!
# Exact geometry of Sargos's D transformation

These are rational identities and a consumer of an explicitly supplied
beta estimate. The analytic D-process estimate is not proved in this module.
The formula is the frozen paper's D-process lemma (Sargos 1995, Theorem 7.1).
-/

noncomputable section

open Expdb
open scoped NNReal

namespace TaoTrudgianYang2025

def sargosDProcessK (k l : ℝ) : ℝ := (5*k+l+2)/(8*(5*k+3*l+2))
def sargosDProcessL (k l : ℝ) : ℝ := (29*k+21*l+10)/(8*(5*k+3*l+2))

theorem sargosDProcess_denominator_pos {k l : ℝ} (hk : 0 ≤ k) (hl : 0 ≤ l) :
    0 < 8*(5*k+3*l+2) := by positivity

theorem sargosDProcess_inTriangle {k l : ℝ} (hk : 0 ≤ k) (hl : 0 ≤ l) :
    InExponentPairTriangle (sargosDProcessK k l) (sargosDProcessL k l) := by
  have hd := sargosDProcess_denominator_pos hk hl
  unfold InExponentPairTriangle sargosDProcessK sargosDProcessL
  refine ⟨by positivity,?_,?_,?_,?_⟩
  · apply (div_le_iff₀ hd).mpr
    linarith
  · apply (le_div_iff₀ hd).mpr
    linarith
  · apply (div_le_iff₀ hd).mpr
    linarith
  · rw [← add_div]
    apply (div_le_iff₀ hd).mpr
    linarith

theorem sargosDProcess_slope {k l : ℝ} (hk : 0 ≤ k) (hl : 0 ≤ l) :
    1/2 ≤ sargosDProcessL k l-sargosDProcessK k l := by
  have hd := sargosDProcess_denominator_pos hk hl
  unfold sargosDProcessK sargosDProcessL
  rw [← sub_div]
  apply (le_div_iff₀ hd).mpr
  linarith

theorem sargosDProcess_zero_gap {k l : ℝ} (hk : 0 ≤ k) (hl : 0 ≤ l) :
    sargosDProcessK k l-1/12 = (5*k-3*l+2)/(24*(5*k+3*l+2)) := by
  have hd : 5*k+3*l+2 ≠ 0 := by positivity
  unfold sargosDProcessK
  field_simp
  ring

theorem sargosDProcess_half_gap {k l : ℝ} (hk : 0 ≤ k) (hl : 0 ≤ l) :
    (sargosDProcessK k l+sargosDProcessL k l)/2-5/12 =
      (k+3*l-2)/(24*(5*k+3*l+2)) := by
  have hd : 5*k+3*l+2 ≠ 0 := by positivity
  unfold sargosDProcessK sargosDProcessL
  field_simp
  ring

theorem sargosDProcess_secondary_le {k l α : ℝ}
    (hk : 0 ≤ k) (hl : 0 ≤ l) (hzero : 0 ≤ 5*k-3*l+2)
    (hhalf : 2 ≤ k+3*l) (hα : 0 ≤ α) (hαhalf : α ≤ 1/2) :
    1/12+2/3*α ≤ exponentPairLine (sargosDProcessK k l) (sargosDProcessL k l) α := by
  have h₀ : 0 ≤ sargosDProcessK k l-1/12 := by
    rw [sargosDProcess_zero_gap hk hl]
    exact div_nonneg hzero (by positivity)
  have h₁ : 0 ≤ (sargosDProcessK k l+sargosDProcessL k l)/2-5/12 := by
    rw [sargosDProcess_half_gap hk hl]
    exact div_nonneg (by linarith) (by positivity)
  have hleft := mul_nonneg h₀ (show 0 ≤ 1-2*α by linarith)
  have hright := mul_nonneg h₁ (show 0 ≤ 2*α by linarith)
  unfold exponentPairLine
  nlinarith only [hleft,hright]

/-- This consumer is conditional on the displayed source beta estimate;
it does not assert that the D-process estimate has been proved. -/
theorem sargosDProcess_pair_of_beta_bound {k l : ℝ}
    (hk : 0 ≤ k) (hl : 0 ≤ l) (hzero : 0 ≤ 5*k-3*l+2)
    (hhalf : 2 ≤ k+3*l)
    (hbeta : ∀ α : ℝ≥0, (α:ℝ) ≤ 1/2 →
      exponentSumGrowthExponent α ≤
        max (exponentPairLine (sargosDProcessK k l) (sargosDProcessL k l) α)
          (1/12+2/3*(α:ℝ))) :
    ExponentPair (sargosDProcessK k l) (sargosDProcessL k l) := by
  apply exponentPair_of_beta_bound_half (sargosDProcess_inTriangle hk hl)
    (sargosDProcess_slope hk hl)
  intro α hα
  have h := hbeta α hα
  rw [max_eq_left (sargosDProcess_secondary_le hk hl hzero hhalf α.coe_nonneg hα)] at h
  exact h

end TaoTrudgianYang2025
