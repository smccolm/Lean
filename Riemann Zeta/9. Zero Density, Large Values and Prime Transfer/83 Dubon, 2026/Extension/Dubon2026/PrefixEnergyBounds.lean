import Dubon2026.HarmonicPowerEnergy
import Mathlib.Algebra.BigOperators.Module

/-! # Global weighted-energy bounds from an actual cumulative square-sum bound

This is a conditional downstream consequence of a Rankin–Selberg mean-square
estimate. The hypothesis concerns the unweighted partial sums, not H1.
-/

namespace Dubon2026

open Filter
open scoped Topology

theorem sum_range_weighted_le_of_prefix_le {b c w : ℕ → ℝ} (N : ℕ)
    (hb : ∀ k ≤ N, (∑ i ∈ Finset.range k, b i) ≤ ∑ i ∈ Finset.range k, c i)
    (hw : ∀ i, 0 ≤ w i) (hm : Antitone w) :
    (∑ i ∈ Finset.range N, w i * b i) ≤ ∑ i ∈ Finset.range N, w i * c i := by
  have hleft := Finset.sum_range_by_parts w b N
  have hright := Finset.sum_range_by_parts w c N
  simp only [smul_eq_mul] at hleft hright
  have ht := mul_le_mul_of_nonneg_left (hb N le_rfl) (hw (N - 1))
  have hs : (∑ i ∈ Finset.range (N - 1),
      (w (i + 1) - w i) * ∑ j ∈ Finset.range (i + 1), c j) ≤
      ∑ i ∈ Finset.range (N - 1),
        (w (i + 1) - w i) * ∑ j ∈ Finset.range (i + 1), b j := by
    apply Finset.sum_le_sum
    intro i hi
    have hiN := Finset.mem_range.mp hi
    exact mul_le_mul_of_nonpos_left (hb (i + 1) (by omega))
      (sub_nonpos.mpr (hm (by omega)))
  linarith

theorem sum_Icc_one_eq_range_succ (f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, f n) = ∑ n ∈ Finset.range N, f (n + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, Nat.add_comm 1]

theorem coefficientEnergy_le_of_prefix_bound_nonneg {a : ℕ → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ N : ℕ, (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) ≤ C * N)
    (N : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) :
    coefficientEnergy a N σ ≤
      C * ((N : ℝ) ^ (max (-2 * σ + 1) 0) * (harmonic N : ℝ)) := by
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
  apply hs.trans (mul_le_mul_of_nonneg_left ?_ hC)
  simpa only [coefficientEnergy, norm_one, one_pow, one_mul] using
    coefficientEnergy_le_power_harmonic (a := fun _ => (1 : ℂ)) (by simp) N σ

theorem coefficientEnergy_le_of_prefix_bound_nonpos {a : ℕ → ℂ} {C : ℝ}
    (ha : ∀ N : ℕ, (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) ≤ C * N)
    {N : ℕ} (hN : 1 ≤ N) {σ : ℝ} (hσ : σ ≤ 0) :
    coefficientEnergy a N σ ≤ C * (N : ℝ) ^ (-2 * σ + 1) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    coefficientEnergy a N σ ≤ ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (N : ℝ) ^ (-2 * σ) := by
      apply Finset.sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg n)
        (by exact_mod_cast (Finset.mem_Icc.mp hn).2) (by linarith)) (sq_nonneg _)
    _ = (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) * (N : ℝ) ^ (-2 * σ) := by rw [Finset.sum_mul]
    _ ≤ (C * N) * (N : ℝ) ^ (-2 * σ) :=
      mul_le_mul_of_nonneg_right (ha N) (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    _ = _ := by rw [Real.rpow_add_one hN0.ne']; ring

/-- A single harmonic majorant covers both signs and the critical exponent. -/
theorem coefficientEnergy_le_of_prefix_bound {a : ℕ → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ N : ℕ, (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) ≤ C * N)
    {N : ℕ} (hN : 1 ≤ N) (σ : ℝ) :
    coefficientEnergy a N σ ≤
      C * ((N : ℝ) ^ (max (-2 * σ + 1) 0) * (harmonic N : ℝ)) := by
  by_cases hs : 0 ≤ σ
  · exact coefficientEnergy_le_of_prefix_bound_nonneg hC ha N hs
  · have he := coefficientEnergy_le_of_prefix_bound_nonpos ha hN (le_of_not_ge hs)
    rw [max_eq_left (by linarith : 0 ≤ -2 * σ + 1)]
    apply he.trans
    have hh := mul_le_mul_of_nonneg_left (one_le_real_harmonic hN)
      (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg N) (-2 * σ + 1)))
    simpa only [mul_one, mul_assoc] using hh

end Dubon2026
