import Tao2026.VinogradovPhase

/-!
# Type I reciprocal-phase reduction

This module records the exact finite rearrangement used in the Type I part of
Proposition 1.12.  The inner support may depend on the outer divisor, matching
the source interval `(1/m) I`.  Each inner phase is rescaled to parameters
`N/m` and `M/m^j`, and the outer coefficients are removed by the triangle
inequality with an explicit uniform envelope.
-/

open Complex Finset
open scoped BigOperators

namespace Tao2026

noncomputable section

/-- The inner Type I sum at the outer divisor `m`. -/
def typeIInnerSum (S : ℕ → Finset ℕ) (N M : ℝ)
    (j m : ℕ) : ℂ :=
  ∑ n ∈ S m,
    standardAdditiveCharacter (reciprocalPhase N M j (m * n))

/-- Exact rescaling of a Type I inner sum to the integer exponential sum with
parameters `N/m` and `M/m^j` used by the source. -/
theorem typeIInnerSum_rescale
    (S : ℕ → Finset ℕ) (N M : ℝ) (j m : ℕ) :
    typeIInnerSum S N M j m =
      ∑ n ∈ S m,
        standardAdditiveCharacter
          (reciprocalPhase (N / m) (M / (m : ℝ) ^ j) j n) := by
  unfold typeIInnerSum
  apply Finset.sum_congr rfl
  intro n hn
  rw [reciprocalPhase_mul_rescale]

/-- The finite Type I bilinear sum before applying the triangle inequality. -/
def typeIOuterSum (K : Finset ℕ) (S : ℕ → Finset ℕ)
    (α : ℕ → ℂ) (N M : ℝ) (j : ℕ) : ℂ :=
  ∑ m ∈ K, α m * typeIInnerSum S N M j m

/-- The exact coefficient-envelope triangle reduction used before applying
the integer exponential-sum estimate to each rescaled Type I inner sum. -/
theorem norm_typeIOuterSum_le
    (K : Finset ℕ) (S : ℕ → Finset ℕ) (α : ℕ → ℂ)
    (N M : ℝ) (j : ℕ) {L : ℝ}
    (hα : ∀ m ∈ K, ‖α m‖ ≤ L) :
    ‖typeIOuterSum K S α N M j‖ ≤
      L * ∑ m ∈ K, ‖typeIInnerSum S N M j m‖ := by
  unfold typeIOuterSum
  calc
    ‖∑ m ∈ K, α m * typeIInnerSum S N M j m‖ ≤
        ∑ m ∈ K, ‖α m * typeIInnerSum S N M j m‖ :=
      norm_sum_le K _
    _ ≤ ∑ m ∈ K, L * ‖typeIInnerSum S N M j m‖ := by
      apply Finset.sum_le_sum
      intro m hm
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hα m hm) (norm_nonneg _)
    _ = L * ∑ m ∈ K, ‖typeIInnerSum S N M j m‖ := by
      rw [Finset.mul_sum]

/-- Combined Type I reduction with the rescaled inner phases exposed in the
conclusion. -/
theorem norm_typeIOuterSum_le_rescaled
    (K : Finset ℕ) (S : ℕ → Finset ℕ) (α : ℕ → ℂ)
    (N M : ℝ) (j : ℕ) {L : ℝ}
    (hα : ∀ m ∈ K, ‖α m‖ ≤ L) :
    ‖typeIOuterSum K S α N M j‖ ≤
      L * ∑ m ∈ K,
        ‖∑ n ∈ S m,
          standardAdditiveCharacter
            (reciprocalPhase (N / m) (M / (m : ℝ) ^ j) j n)‖ := by
  simpa only [typeIInnerSum_rescale] using
    norm_typeIOuterSum_le K S α N M j hα

end

end Tao2026
