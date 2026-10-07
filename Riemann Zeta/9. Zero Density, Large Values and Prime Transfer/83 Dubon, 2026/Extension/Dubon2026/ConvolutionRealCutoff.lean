import Dubon2026.ConvolutionSummatory
import Mathlib.Algebra.Order.Floor.Semifield

/-! # Genuine Dirichlet convolution summation at real cutoffs -/

namespace Dubon2026

open Complex

noncomputable section

/-- The literal positive-index complex coefficient sum at a real cutoff. -/
def complexCoefficientSummatory (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n

/-- In the real-cutoff hyperbola formula, every index outside the actual finite support contributes zero. -/
theorem complexCoefficientSummatory_div_eq_zero (a : ℕ → ℂ) (x : ℝ) {n : ℕ}
    (hn : n ∉ Finset.Icc 1 ⌊x⌋₊) : complexCoefficientSummatory a (x / n) = 0 := by
  by_cases hn0 : n = 0
  · simp [hn0, complexCoefficientSummatory]
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    have hnx : ⌊x⌋₊ < n := by simpa only [Finset.mem_Icc, hn1, true_and, not_le] using hn
    have hxn : x < (n : ℝ) := Nat.lt_of_floor_lt hnx
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
    have hfloor : ⌊x / (n : ℝ)⌋₊ = 0 := Nat.floor_eq_zero.mpr ((div_lt_one hnR).mpr hxn)
    simp [complexCoefficientSummatory, hfloor]

/-- The actual finite convolution sum equals the absolutely convergent, finitely supported hyperbola series at every real cutoff. -/
theorem hasSum_complexCoefficientSummatory_convolution (a b : ℕ → ℂ) (x : ℝ) :
    HasSum (fun n : ℕ => a n * complexCoefficientSummatory b (x / n))
      (complexCoefficientSummatory (LSeries.convolution a b) x) := by
  have hs : HasSum (fun n : ℕ => a n * complexCoefficientSummatory b (x / n))
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n * complexCoefficientSummatory b (x / n)) :=
    hasSum_sum_of_ne_finset_zero (s := Finset.Icc 1 ⌊x⌋₊)
    (f := fun n : ℕ => a n * complexCoefficientSummatory b (x / n))
    (fun n hn => by dsimp only; rw [complexCoefficientSummatory_div_eq_zero b x hn, mul_zero])
  convert hs using 1
  rw [complexCoefficientSummatory, sum_convolution_Icc]
  simp only [complexCoefficientSummatory, Nat.floor_div_natCast]

/-- The reciprocal coefficient series gives exactly the linear term of a real-cutoff convolution. -/
theorem hasSum_convolution_linear {a : ℕ → ℂ} (ha : LSeriesSummable a 1) (c : ℂ) (x : ℝ) :
    HasSum (fun n : ℕ => a n * (c * ((x / n : ℝ) : ℂ))) (c * (x : ℂ) * LSeries a 1) := by
  convert ha.hasSum.mul_left (c * (x : ℂ)) using 1
  funext n
  by_cases hn : n = 0
  · simp [hn]
  · rw [LSeries.term_of_ne_zero hn, Complex.cpow_one]
    push_cast
    ring

end
end Dubon2026
