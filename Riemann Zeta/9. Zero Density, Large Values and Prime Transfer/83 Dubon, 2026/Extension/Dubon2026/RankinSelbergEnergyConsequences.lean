import Dubon2026.WeightedEnergyAsymptotic
import Dubon2026.MeanSquareEnergy
import Mathlib.Analysis.PSeries

/-! # Exact downstream energy consequences of the cumulative Rankin–Selberg estimate

The actual modular Rankin–Selberg theorem remains an upstream obligation. These
statements consume a pointwise cumulative remainder and prove the weighted conclusions.
-/

namespace Dubon2026

open Filter Set MeasureTheory
open scoped Topology

noncomputable section

theorem coefficientEnergy_le_const_power_sum {a : ℕ → ℂ} {C : ℝ}
    (ha : ∀ N : ℕ, (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) ≤ C * N)
    (N : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) :
    coefficientEnergy a N σ ≤
      C * ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-2 * σ) := by
  have hb : ∀ k ≤ N, (∑ i ∈ Finset.range k, ‖a (i + 1)‖ ^ 2) ≤
      ∑ i ∈ Finset.range k, C := by
    intro k _
    rw [← sum_Icc_one_eq_range_succ (fun n => ‖a n‖ ^ 2) k]
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm C] using ha k
  have hw : Antitone (fun i : ℕ => ((i + 1 : ℕ) : ℝ) ^ (-2 * σ)) := by
    intro i j hij
    apply Real.rpow_le_rpow_of_nonpos (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
    linarith
  have hh := sum_range_weighted_le_of_prefix_le N hb
    (fun i => Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (i + 1 : ℕ)) _) hw
  have hs : coefficientEnergy a N σ ≤ C * ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-2 * σ) := by
    rw [coefficientEnergy, sum_Icc_one_eq_range_succ, sum_Icc_one_eq_range_succ,
      Finset.mul_sum]
    simpa only [mul_comm] using hh
  exact hs

theorem mean_square_limit_of_remainder {a : ℕ → ℂ} {c C β : ℝ} (hβ : β < 1)
    (he : ∀ x : ℝ, 1 ≤ x → |squareSummatory a x - c * x| ≤ C * x ^ β) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) / N) atTop (𝓝 c) := by
  have hh := ((tendsto_rpow_neg_atTop (sub_pos.mpr hβ)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul C
  simp only [mul_zero] at hh
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hh
    (Eventually.of_forall fun _ => norm_nonneg _) ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hb := div_le_div_of_nonneg_right (he N (by exact_mod_cast hN)) hN0.le
  rw [squareSummatory_nat] at hb
  have hleft : (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) / (N : ℝ) - c =
      ((∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) - c * N) / N := by field_simp
  rw [Real.norm_eq_abs, hleft, abs_div, abs_of_pos hN0]
  simp only [Function.comp_def]
  convert hb using 1
  rw [show -(1 - β) = β - 1 by ring, Real.rpow_sub hN0, Real.rpow_one]
  ring

theorem weighted_energy_right_of_mean {a : ℕ → ℂ} {c σ : ℝ}
    (hmean : Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) / N) atTop (𝓝 c))
    (hσ : 1 / 2 < σ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 0 ≤ coefficientEnergy a N σ ∧ coefficientEnergy a N σ ≤ B := by
  obtain ⟨C, hC, hb⟩ := exists_prefix_square_bound_of_mean hmean
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-2 * σ)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  refine ⟨C * ∑' n : ℕ, (n : ℝ) ^ (-2 * σ),
    mul_nonneg hC.le (tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)), ?_⟩
  intro N
  refine ⟨coefficientEnergy_nonneg _ _ _, ?_⟩
  apply (coefficientEnergy_le_const_power_sum hb N (by linarith : 0 ≤ σ)).trans
  exact mul_le_mul_of_nonneg_left (Summable.sum_le_tsum (Finset.Icc 1 N)
    (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _) hs) hC.le

/-- All three regimes of the printed weighted-energy lemma, from its exact 3/5 remainder input. -/
theorem rankin_selberg_weighted_energy {a : ℕ → ℂ} {c C : ℝ} (hC : 0 ≤ C)
    (he : ∀ x : ℝ, 1 ≤ x → |squareSummatory a x - c * x| ≤ C * x ^ (3 / 5 : ℝ)) :
    (∀ σ : ℝ, σ < 1 / 2 → Tendsto (fun N : ℕ => (coefficientEnergy a N σ -
      c * (N : ℝ) ^ (1 - 2 * σ) / (1 - 2 * σ)) /
        (N : ℝ) ^ (1 - 2 * σ)) atTop (𝓝 0)) ∧
    (∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N →
      |coefficientEnergy a N (1 / 2) - c * Real.log N| ≤ B) ∧
    (∀ σ : ℝ, 1 / 2 < σ → ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ,
      0 ≤ coefficientEnergy a N σ ∧ coefficientEnergy a N σ ≤ B) := by
  refine ⟨fun σ hσ => weighted_energy_left_of_remainder (by norm_num) hσ he, ?_, ?_⟩
  · refine ⟨|c| + C * (1 + 1 / (1 - (3 / 5 : ℝ))), by positivity, ?_⟩
    intro N hN
    exact weighted_energy_center_of_remainder hC (by norm_num) he hN
  · intro σ hσ
    exact weighted_energy_right_of_mean (mean_square_limit_of_remainder (by norm_num) he) hσ

end

end Dubon2026
