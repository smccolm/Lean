import Dubon2026.CoprimeWeightSum
import Mathlib.NumberTheory.LSeries.Convolution

/-! # Exact finite hyperbola summation for the genuine Dirichlet convolution -/

namespace Dubon2026

open Finset

/-- Every positive-index convolution partial sum is the exact hyperbola sum of the original coefficients. -/
theorem sum_convolution_Icc {R : Type*} [Semiring R] (a b : ℕ → R) (N : ℕ) :
    (∑ n ∈ Icc 1 N, LSeries.convolution a b n) =
      ∑ d ∈ Icc 1 N, a d * ∑ n ∈ Icc 1 (N / d), b n := by
  classical
  have hdset {n : ℕ} (hn : n ∈ Icc 1 N) :
      n.divisors = (Icc 1 N).filter (fun d => d ∣ n) := by
    ext d
    constructor
    · intro hd
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,
        (Nat.divisor_le hd).trans (mem_Icc.mp hn).2⟩, Nat.dvd_of_mem_divisors hd⟩
    · intro hd
      exact Nat.mem_divisors.mpr ⟨(mem_filter.mp hd).2, by have := (mem_Icc.mp hn).1; omega⟩
  calc
    _ = ∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, a d * b (n / d) := by
      apply sum_congr rfl
      intro n _
      simp only [LSeries.convolution_def]
      exact Nat.sum_divisorsAntidiagonal (fun d m => a d * b m)
    _ = ∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N, if d ∣ n then a d * b (n / d) else 0 := by
      apply sum_congr rfl
      intro n hn
      rw [hdset hn, sum_filter]
    _ = ∑ d ∈ Icc 1 N, ∑ n ∈ (Icc 1 N).filter (fun n => d ∣ n), a d * b (n / d) := by
      rw [sum_comm]
      simp only [sum_filter]
    _ = _ := by
      apply sum_congr rfl
      intro d hd
      have hd0 : 0 < d := (mem_Icc.mp hd).1
      rw [filter_dvd_Icc_eq_image hd0, sum_image]
      · simp only [Nat.mul_div_cancel_left _ hd0, ← mul_sum]
      · intro u _ v _ huv
        exact Nat.eq_of_mul_eq_mul_left hd0 huv

/-- A genuine linear partial-sum bound is preserved by convolution with a nonnegative absolutely summable reciprocal weight. -/
theorem sum_convolution_le_linear {a b : ℕ → ℝ} {B : ℝ}
    (ha : ∀ n, 0 ≤ a n) (hB : 0 ≤ B)
    (hb : ∀ N : ℕ, (∑ n ∈ Icc 1 N, b n) ≤ B * N)
    (hs : Summable (fun n : ℕ => a n / (n : ℝ))) (N : ℕ) :
    (∑ n ∈ Icc 1 N, LSeries.convolution a b n) ≤
      B * N * ∑' n : ℕ, a n / (n : ℝ) := by
  rw [sum_convolution_Icc]
  calc
    _ ≤ ∑ d ∈ Icc 1 N, a d * (B * (N / d : ℕ)) := by
      apply sum_le_sum
      intro d _
      exact mul_le_mul_of_nonneg_left (hb (N / d)) (ha d)
    _ ≤ ∑ d ∈ Icc 1 N, a d * (B * ((N : ℝ) / d)) := by
      apply sum_le_sum
      intro d _
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left Nat.cast_div_le hB) (ha d)
    _ = B * N * ∑ d ∈ Icc 1 N, a d / (d : ℝ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro d _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (hs.sum_le_tsum (Icc 1 N) (fun n _ => div_nonneg (ha n) (Nat.cast_nonneg n))) (by positivity)

end Dubon2026
