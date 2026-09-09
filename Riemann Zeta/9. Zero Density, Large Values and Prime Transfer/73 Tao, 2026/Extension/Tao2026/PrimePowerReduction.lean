import Tao2026.PrimeIntervals
import Tao2026.VaughanIdentity

/-!
# Removing higher prime powers from the Mangoldt phase sum

The proof of Theorem 2.5 passes from a prime sum weighted by `log p` to a
von-Mangoldt sum and declares the remaining prime powers negligible.  This
module records that passage exactly and bounds the oscillatory tail by the
already formalized local prime-power majorant.
-/

open Finset
open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace Tao2026

noncomputable section

/-- Prime-supported logarithmically weighted reciprocal-phase sum over an
arbitrary finite set. -/
def primeLogReciprocalPhaseSum
    (s : Finset ℕ) (N M : ℝ) (j : ℕ) : ℂ :=
  ∑ n ∈ s.filter Nat.Prime,
    (Real.log n : ℂ) * standardAdditiveCharacter (reciprocalPhase N M j n)

/-- Logarithmically weighted prime-sum form of the source's reduction from
`j = 1` to `j = 2` with the reciprocal-linear coefficients absorbed. -/
theorem primeLogReciprocalPhaseSum_one_eq_absorb
    (s : Finset ℕ) (N M : ℝ) :
    primeLogReciprocalPhaseSum s N M 1 =
      primeLogReciprocalPhaseSum s (N + M) 0 2 := by
  unfold primeLogReciprocalPhaseSum
  apply Finset.sum_congr rfl
  intro n _hn
  rw [reciprocalPhase_one_eq_absorb]

/-- The complementary non-prime part of the Mangoldt phase sum. -/
def primePowerTailReciprocalPhaseSum
    (s : Finset ℕ) (N M : ℝ) (j : ℕ) : ℂ :=
  ∑ n ∈ s.filter (fun n => ¬n.Prime),
    (Λ n : ℂ) * standardAdditiveCharacter (reciprocalPhase N M j n)

/-- Exact prime/higher-prime-power split of a finite Mangoldt phase sum. -/
theorem weightedMangoldtSum_eq_primeLog_add_primePowerTail
    (s : Finset ℕ) (N M : ℝ) (j : ℕ) :
    weightedRealArithmeticSum s
        (fun n => standardAdditiveCharacter (reciprocalPhase N M j n)) Λ =
      primeLogReciprocalPhaseSum s N M j +
        primePowerTailReciprocalPhaseSum s N M j := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not s Nat.Prime
    (fun n => (Λ n : ℂ) *
      standardAdditiveCharacter (reciprocalPhase N M j n))
  calc
    weightedRealArithmeticSum s
        (fun n => standardAdditiveCharacter (reciprocalPhase N M j n)) Λ =
      ∑ n ∈ s, (Λ n : ℂ) *
        standardAdditiveCharacter (reciprocalPhase N M j n) := rfl
    _ = (∑ n ∈ s.filter Nat.Prime,
          (Λ n : ℂ) * standardAdditiveCharacter (reciprocalPhase N M j n)) +
        ∑ n ∈ s.filter (fun n => ¬n.Prime),
          (Λ n : ℂ) * standardAdditiveCharacter (reciprocalPhase N M j n) :=
      hsplit.symm
    _ = primeLogReciprocalPhaseSum s N M j +
        primePowerTailReciprocalPhaseSum s N M j := by
      rw [primeLogReciprocalPhaseSum, primePowerTailReciprocalPhaseSum]
      congr 1
      apply Finset.sum_congr rfl
      intro n hn
      rw [ArithmeticFunction.vonMangoldt_apply_prime
        (Finset.mem_filter.mp hn).2]

/-- Oscillation cannot enlarge the non-prime Mangoldt tail. -/
theorem norm_primePowerTailReciprocalPhaseSum_le
    (s : Finset ℕ) (N M : ℝ) (j : ℕ) :
    ‖primePowerTailReciprocalPhaseSum s N M j‖ ≤
      ∑ n ∈ s.filter (fun n => ¬n.Prime), Λ n := by
  rw [primePowerTailReciprocalPhaseSum]
  calc
    ‖∑ n ∈ s.filter (fun n => ¬n.Prime),
        (Λ n : ℂ) * standardAdditiveCharacter (reciprocalPhase N M j n)‖ ≤
      ∑ n ∈ s.filter (fun n => ¬n.Prime),
        ‖(Λ n : ℂ) *
          standardAdditiveCharacter (reciprocalPhase N M j n)‖ :=
      norm_sum_le _ _
    _ = ∑ n ∈ s.filter (fun n => ¬n.Prime), Λ n := by
      apply Finset.sum_congr rfl
      intro n _hn
      rw [norm_mul, norm_standardAdditiveCharacter, mul_one,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]

/-- Exact interval used by the local prime-power theorem. -/
def intervalPrimePowerTailReciprocalPhaseSum
    (a y N M : ℝ) (j : ℕ) : ℂ :=
  primePowerTailReciprocalPhaseSum
    (Finset.Ioc ⌊a⌋₊ ⌊a + y⌋₊) N M j

/-- The reciprocal phase has unit modulus, so the oscillatory interval tail
is bounded by the exact unweighted tail from `GafniTao.LocalCover`. -/
theorem norm_intervalPrimePowerTailReciprocalPhaseSum_le
    (a y N M : ℝ) (j : ℕ) :
    ‖intervalPrimePowerTailReciprocalPhaseSum a y N M j‖ ≤
      GafniTao.primePowerTailIntervalSum a y := by
  exact norm_primePowerTailReciprocalPhaseSum_le
    (Finset.Ioc ⌊a⌋₊ ⌊a + y⌋₊) N M j

/-- Fully explicit local higher-prime-power error bound. -/
theorem norm_intervalPrimePowerTailReciprocalPhaseSum_le_explicit
    {a y : ℝ} (N M : ℝ) (j : ℕ) (ha : 1 ≤ a) (hy : 0 ≤ y) :
    ‖intervalPrimePowerTailReciprocalPhaseSum a y N M j‖ ≤
      (⌊Real.log (a + y) / Real.log 2⌋₊ : ℝ) *
        ((a ^ (-(1 / 2 : ℝ)) * y + 1) * Real.log (a + y)) := by
  exact (norm_intervalPrimePowerTailReciprocalPhaseSum_le a y N M j).trans
    (GafniTao.primePowerTailIntervalSum_le ha hy)

end

end Tao2026
