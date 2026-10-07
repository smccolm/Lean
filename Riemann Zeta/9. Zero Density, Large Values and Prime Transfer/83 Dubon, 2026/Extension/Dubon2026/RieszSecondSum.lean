import Dubon2026.RieszSecondKernel
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Exact finite Riesz sums and the positive-coefficient smoothing inequalities -/

namespace Dubon2026

open Finset

noncomputable section

/-- The literal positive-index partial sum of a real coefficient sequence at a real cutoff. -/
def realCoefficientSummatory (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, a n

/-- The actual second Riesz mean with its factorial-normalized quadratic weights. -/
def rieszSecondSum (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 ⌊x⌋₊, a n * rieszSecondKernel (x - n)

/-- The kernel definition agrees exactly with the usual finite quadratic Riesz sum. -/
theorem rieszSecondSum_eq (a : ℕ → ℝ) (x : ℝ) :
    rieszSecondSum a x = ∑ n ∈ Icc 1 ⌊x⌋₊, a n * (x - n) ^ 2 / 2 := by
  apply sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
  rw [rieszSecondKernel_eq (sub_nonneg.mpr ((Nat.le_floor_iff' hn0).mp (mem_Icc.mp hn).2))]
  ring

/-- Enlarging the finite support cutoff leaves the actual Riesz sum unchanged, because the added weights vanish. -/
theorem rieszSecondSum_eq_sum_of_le (a : ℕ → ℝ) {x y : ℝ} (hxy : x ≤ y) :
    rieszSecondSum a x = ∑ n ∈ Icc 1 ⌊y⌋₊, a n * rieszSecondKernel (x - n) := by
  apply sum_subset (Icc_subset_Icc_right (Nat.floor_mono hxy))
  intro n hn hn'
  have hnx : ⌊x⌋₊ < n := by
    have hn1 := (mem_Icc.mp hn).1
    simp only [mem_Icc, hn1, true_and, not_le] at hn'
    exact hn'
  rw [rieszSecondKernel_eq_zero (sub_nonpos.mpr (Nat.lt_of_floor_lt hnx).le), mul_zero]

/-- All three finite sums in a second difference have one exact common-support expansion. -/
theorem rieszSecondSum_difference_eq (a : ℕ → ℝ) (x : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    rieszSecondDifference (rieszSecondSum a) x h =
      ∑ n ∈ Icc 1 ⌊x + 2 * h⌋₊, a n * rieszSecondDifference rieszSecondKernel (x - n) h := by
  have h0 := rieszSecondSum_eq_sum_of_le a (show x ≤ x + 2 * h by linarith)
  have h1 := rieszSecondSum_eq_sum_of_le a (show x + h ≤ x + 2 * h by linarith)
  rw [rieszSecondDifference, h0, h1, rieszSecondSum]
  rw [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro n _
  have he1 : x + h - n = x - n + h := by ring
  have he2 : x + 2 * h - n = x - n + 2 * h := by ring
  simp only [rieszSecondDifference, he1, he2]
  ring

/-- Positivity bounds the actual smoothed difference above by the true upper-cutoff coefficient sum. -/
theorem rieszSecondSum_difference_le {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (x : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    rieszSecondDifference (rieszSecondSum a) x h ≤ h ^ 2 * realCoefficientSummatory a (x + 2 * h) := by
  rw [rieszSecondSum_difference_eq a x hh, realCoefficientSummatory, mul_sum]
  apply sum_le_sum
  intro n _
  exact (mul_le_mul_of_nonneg_left (rieszSecondKernel_difference_bounds hh).2 (ha n)).trans_eq
    (mul_comm _ _)

/-- Positivity bounds the actual smoothed difference below by the true lower-cutoff coefficient sum. -/
theorem le_rieszSecondSum_difference {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (x : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    h ^ 2 * realCoefficientSummatory a x ≤ rieszSecondDifference (rieszSecondSum a) x h := by
  rw [rieszSecondSum_difference_eq a x hh, realCoefficientSummatory, mul_sum]
  calc
    _ = ∑ n ∈ Icc 1 ⌊x⌋₊, a n * rieszSecondDifference rieszSecondKernel (x - n) h := by
      apply sum_congr rfl
      intro n hn
      have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
      rw [rieszSecondKernel_difference_eq
        (sub_nonneg.mpr ((Nat.le_floor_iff' hn0).mp (mem_Icc.mp hn).2)) hh, mul_comm]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg
      (Icc_subset_Icc_right (Nat.floor_mono (show x ≤ x + 2 * h by linarith)))
      (fun n _ _ => mul_nonneg (ha n) (rieszSecondKernel_difference_bounds hh).1)

/-- The genuine unsmoothed partial sum lies between backward and forward second Riesz differences. -/
theorem realCoefficientSummatory_riesz_bounds {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (x : ℝ) {h : ℝ} (hh : 0 < h) :
    rieszSecondDifference (rieszSecondSum a) (x - 2 * h) h / h ^ 2 ≤ realCoefficientSummatory a x ∧
      realCoefficientSummatory a x ≤ rieszSecondDifference (rieszSecondSum a) x h / h ^ 2 := by
  have hsq : 0 < h ^ 2 := sq_pos_of_pos hh
  constructor
  · apply (div_le_iff₀ hsq).mpr
    have hb := rieszSecondSum_difference_le ha (x - 2 * h) hh.le
    rw [sub_add_cancel] at hb
    simpa only [mul_comm] using hb
  · apply (le_div_iff₀ hsq).mpr
    simpa only [mul_comm] using le_rieszSecondSum_difference ha x hh.le

end
end Dubon2026
