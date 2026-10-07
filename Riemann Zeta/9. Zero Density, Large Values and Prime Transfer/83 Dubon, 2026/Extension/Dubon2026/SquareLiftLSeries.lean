import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-! # The literal square-supported coefficient lift and its Dirichlet series -/

namespace Dubon2026

noncomputable section

/-- Put the actual coefficient at n², and zero at nonsquares. -/
def squareLiftCoefficients (a : ℕ → ℂ) : ℕ → ℂ :=
  Function.extend (fun n : ℕ => n ^ 2) a 0

/-- The square lift returns the original coefficient at every square. -/
theorem squareLiftCoefficients_sq (a : ℕ → ℂ) (n : ℕ) :
    squareLiftCoefficients a (n ^ 2) = a n :=
  (Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0)).extend_apply a 0 n

/-- The square lift is zero at every nonsquare. -/
theorem squareLiftCoefficients_eq_zero (a : ℕ → ℂ) {n : ℕ}
    (hn : n ∉ Set.range (fun m : ℕ => m ^ 2)) : squareLiftCoefficients a n = 0 :=
  Function.extend_apply' _ _ n hn

/-- The actual L-series summand on squares is exactly the original summand at twice the parameter. -/
theorem lseries_term_squareLift (a : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    LSeries.term (squareLiftCoefficients a) s (n ^ 2) = LSeries.term a (2 * s) n := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [LSeries.term_def, LSeries.term_def, if_neg (pow_ne_zero 2 hn), if_neg hn,
      squareLiftCoefficients_sq, Nat.cast_pow,
      ← Complex.natCast_cpow_natCast_mul n 2 s]
    norm_num

/-- Every L-series summand off the square support vanishes exactly. -/
theorem lseries_term_squareLift_eq_zero (a : ℕ → ℂ) (s : ℂ) {n : ℕ}
    (hn : n ∉ Set.range (fun m : ℕ => m ^ 2)) : LSeries.term (squareLiftCoefficients a) s n = 0 := by
  rw [LSeries.term_def, squareLiftCoefficients_eq_zero a hn]
  split_ifs <;> simp

/-- Absolute convergence of the actual square lift is equivalent to convergence at twice the parameter. -/
theorem lseriesSummable_squareLift_iff (a : ℕ → ℂ) (s : ℂ) :
    LSeriesSummable (squareLiftCoefficients a) s ↔ LSeriesSummable a (2 * s) := by
  have h := (Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0)).summable_iff
    (fun n hn => lseries_term_squareLift_eq_zero a s hn)
  simpa only [Function.comp_def, lseries_term_squareLift, LSeriesSummable] using h.symm

/-- The actual square lift preserves the exact sum, with the parameter multiplied by two. -/
theorem lseriesHasSum_squareLift_iff (a : ℕ → ℂ) (s A : ℂ) :
    LSeriesHasSum (squareLiftCoefficients a) s A ↔ LSeriesHasSum a (2 * s) A := by
  have h := (Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0)).hasSum_iff
    (fun n hn => lseries_term_squareLift_eq_zero a s hn) (a := A)
  simpa only [Function.comp_def, lseries_term_squareLift, LSeriesHasSum] using h.symm

/-- The convergent Dirichlet series of the actual square lift equals the original series at twice the parameter. -/
theorem LSeries_squareLift {a : ℕ → ℂ} {s : ℂ} (ha : LSeriesSummable a (2 * s)) :
    LSeries (squareLiftCoefficients a) s = LSeries a (2 * s) :=
  ((lseriesHasSum_squareLift_iff a s _).mpr ha.LSeriesHasSum).LSeries_eq

end
end Dubon2026
