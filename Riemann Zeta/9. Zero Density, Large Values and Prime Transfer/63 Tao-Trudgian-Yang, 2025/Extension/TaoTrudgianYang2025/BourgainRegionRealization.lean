import TaoTrudgianYang2025.EnergyPoweringLimits

/-!
# Actual region realizations after varying analytic thresholds

The scale threshold and physical tolerance may vary arbitrarily with the
sequence index. Region membership supplies every pattern; the source count
approaches its prescribed exponent while satisfying the selected tolerances.
-/

open Filter Topology
open scoped Classical

noncomputable section

namespace TaoTrudgianYang2025

/-- An explicit scale threshold absorbs one varying multiplicative factor. -/
theorem bourgain_abs_logb_le_of_threshold {N A ε : ℝ}
    (hN : 1 < N) (hε : 0 < ε)
    (hscale : Real.exp (|Real.log A|/ε+1) ≤ N) :
    |Real.logb N A| ≤ ε := by
  rw [Real.logb, abs_div, abs_of_pos (Real.log_pos hN)]
  apply (div_le_iff₀ (Real.log_pos hN)).2
  have hl : |Real.log A|/ε+1 ≤ Real.log N :=
    (Real.le_log_iff_exp_le (zero_lt_one.trans hN)).2 hscale
  have hm := mul_le_mul_of_nonneg_left hl hε.le
  rw [mul_add, mul_div_cancel₀ _ hε.ne'] at hm
  linarith

/-- Source patterns chosen after arbitrary physical tolerances and scale
thresholds. The logarithmic count limit is derived from actual realizability. -/
theorem exists_bourgain_region_family {σ τ ρ energy : ℝ}
    (hregion : InCardinalityEnergyRegion σ τ ρ energy)
    (δ C : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) :
    ∃ P : ℕ → LargeValuePattern,
      Tendsto (fun n => (P n).N) atTop atTop ∧
      Tendsto (fun n => Real.logb (P n).N ((P n).ordinates.card : ℝ))
        atTop (nhds ρ) ∧
      ∀ n, 2 ≤ (P n).N ∧ C n ≤ (P n).N ∧
        (P n).N^(τ-δ n) ≤ (P n).T ∧ (P n).T ≤ (P n).N^(τ+δ n) ∧
        (P n).N^(σ-δ n) ≤ (P n).V ∧ (P n).ordinates.Nonempty ∧
        |Real.logb (P n).N ((P n).ordinates.card : ℝ)-ρ| ≤ poweringAccuracy n := by
  obtain ⟨s, hs⟩ := hregion
  let R : ℕ → ℝ := fun n => max ((n : ℝ)+2) (C n)
  have hR (n : ℕ) : 0 < R n :=
    (show (0 : ℝ) < n+2 by positivity).trans_le (le_max_left _ _)
  have hex (n : ℕ) := hs.2.2.2.2.2
    (poweringAccuracy n) (poweringAccuracy_pos n) (δ n) (hδ n) (R n) (hR n)
  let P : ℕ → LargeValuePattern := fun n => Classical.choose (hex n)
  have hP (n : ℕ) := Classical.choose_spec (hex n)
  change ∀ n, R n ≤ (P n).N ∧ _ at hP
  have hcard (n : ℕ) : (0 : ℝ) < (P n).ordinates.card :=
    (Real.rpow_pos_of_pos (zero_lt_one.trans (P n).one_lt_N) _).trans_le
      (hP n).2.2.2.2.2.1
  refine ⟨P, ?_, ?_, ?_⟩
  · apply tendsto_atTop_mono (fun n => (le_max_left _ _).trans (hP n).1)
    exact tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  · apply tendsto_logb_of_power_sandwich _ _ poweringAccuracy ρ
      (fun n => (P n).one_lt_N) hcard poweringAccuracy_tendsto
    intro n
    exact ⟨(hP n).2.2.2.2.2.1, (hP n).2.2.2.2.2.2.1⟩
  · intro n
    have hlow : ρ-poweringAccuracy n ≤
        Real.logb (P n).N ((P n).ordinates.card : ℝ) :=
      (Real.le_logb_iff_rpow_le (P n).one_lt_N (hcard n)).2 (hP n).2.2.2.2.2.1
    have hupp : Real.logb (P n).N ((P n).ordinates.card : ℝ) ≤
        ρ+poweringAccuracy n :=
      (Real.logb_le_iff_le_rpow (P n).one_lt_N (hcard n)).2 (hP n).2.2.2.2.2.2.1
    refine ⟨?_, (le_max_right _ _).trans (hP n).1,
      (hP n).2.1, (hP n).2.2.1, (hP n).2.2.2.1, ?_, ?_⟩
    · have hn : (n : ℝ)+2 ≤ (P n).N := (le_max_left _ _).trans (hP n).1
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    · exact Finset.card_pos.mp (by exact_mod_cast hcard n)
    · exact abs_le.mpr ⟨by linarith, by linarith⟩

end TaoTrudgianYang2025
