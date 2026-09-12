import Tao2026.BadIntervalMaximal

/-!
# Typical normalized bad intervals

This module gives exact finite contracts for the normalized and typical
intervals in Definitions 6.3--6.4 of Tao's argument.  The source's slowly
varying expressions `z^(1-o(1))` and `z^(1+o(1))` are represented by explicit
natural-number cutoffs.  Thus no asymptotic notation is hidden in a finite
predicate: later estimates must provide the appropriate cutoff functions.

Because the same-window admissibility claim in Lemma 6.2 does not follow from
containment, the base predicate uses the corrected comparable-scale bounds
proved in `NormalizedBadIntervals` and used by `BadIntervalMaximal`.
-/

namespace Tao2026

open scoped BigOperators

/-- Condition (ii) in the definition of a typical normalized interval: no
element of the interval is divisible by the square of an integer at least the
specified threshold. -/
def AvoidsSquareMultiplesAtLeast (N H squareThreshold : ℕ) : Prop :=
  ∀ n ∈ consecutiveInterval N H, ∀ d : ℕ,
    squareThreshold ≤ d → ¬d ^ 2 ∣ n

/-- The exact finite 1000-prime anatomy in condition (iii).  Indices
`0,...,999` represent the source's `p₁,...,p₁₀₀₀`; consequently `factors` is
nonincreasing. -/
structure TypicalPrimeAnatomy
    (lowerPrime upperPrime p₀ m : ℕ) where
  factors : Fin 1000 → ℕ
  remainder : ℕ
  factors_prime : ∀ i, (factors i).Prime
  factors_nonincreasing : ∀ ⦃i j : Fin 1000⦄, i ≤ j → factors j ≤ factors i
  lower_le_last : lowerPrime ≤ factors (Fin.last 999)
  first_le_p₀ : factors 0 ≤ p₀
  p₀_le_upper : p₀ ≤ upperPrime
  factorization : m = (∏ i, factors i) * remainder
  remainder_smooth : IsSmooth remainder (factors (Fin.last 999))

/-- The three finite conditions defining typicality, separated from the
normalized-interval base predicate so that "non-typical" is its literal
negation. -/
def SatisfiesTypicalNormalizedConditions
    (lengthCutoff squareThreshold lowerPrime upperPrime
      N H p₀ m : ℕ) : Prop :=
  H < lengthCutoff ∧
    AvoidsSquareMultiplesAtLeast N H squareThreshold ∧
    Nonempty (TypicalPrimeAnatomy lowerPrime upperPrime p₀ m)

/-- Corrected-scale exact form of a typical normalized bad interval.  The
distinguished squared prime and its cofactor are retained as named data. -/
def IsTypicalScaleNormalizedBadInterval
    (x lengthCutoff squareThreshold lowerPrime upperPrime
      N H p₀ k m : ℕ) : Prop :=
  IsNormalizedBadInterval N H p₀ k m ∧
    x ≤ 4 * N + 1 ∧ N + H ≤ 2 * x ∧
    SatisfiesTypicalNormalizedConditions
      lengthCutoff squareThreshold lowerPrime upperPrime N H p₀ m

/-- A normalized interval is non-typical precisely when at least one of the
three typicality conditions fails. -/
def IsNonTypicalScaleNormalizedBadInterval
    (x lengthCutoff squareThreshold lowerPrime upperPrime
      N H p₀ k m : ℕ) : Prop :=
  IsNormalizedBadInterval N H p₀ k m ∧
    x ≤ 4 * N + 1 ∧ N + H ≤ 2 * x ∧
    ¬SatisfiesTypicalNormalizedConditions
      lengthCutoff squareThreshold lowerPrime upperPrime N H p₀ m

/-- The source subsequently fixes the orientation whose distinguished value
is the left endpoint. -/
def IsForwardTypicalScaleNormalizedBadInterval
    (x lengthCutoff squareThreshold lowerPrime upperPrime
      N H p₀ k m : ℕ) : Prop :=
  IsTypicalScaleNormalizedBadInterval x lengthCutoff squareThreshold
    lowerPrime upperPrime N H p₀ k m ∧ k = N + 1

/-- Every corrected-scale normalized interval is exactly typical or
non-typical for any fixed choice of finite cutoffs. -/
theorem typical_or_nonTypical_of_scaleNormalized
    {x lengthCutoff squareThreshold lowerPrime upperPrime
      N H p₀ k m : ℕ}
    (hnorm : IsNormalizedBadInterval N H p₀ k m)
    (hleft : x ≤ 4 * N + 1) (hright : N + H ≤ 2 * x) :
    IsTypicalScaleNormalizedBadInterval x lengthCutoff squareThreshold
        lowerPrime upperPrime N H p₀ k m ∨
      IsNonTypicalScaleNormalizedBadInterval x lengthCutoff squareThreshold
        lowerPrime upperPrime N H p₀ k m := by
  by_cases htyp : SatisfiesTypicalNormalizedConditions
      lengthCutoff squareThreshold lowerPrime upperPrime N H p₀ m
  · exact Or.inl ⟨hnorm, hleft, hright, htyp⟩
  · exact Or.inr ⟨hnorm, hleft, hright, htyp⟩

/-- Exact three-way split used by Proposition 6.5: a non-typical interval is
too long, contains a forbidden large square multiple, or lacks the required
1000-prime anatomy. -/
theorem IsNonTypicalScaleNormalizedBadInterval.failure_cases
    {x lengthCutoff squareThreshold lowerPrime upperPrime
      N H p₀ k m : ℕ}
    (hnon : IsNonTypicalScaleNormalizedBadInterval x lengthCutoff
      squareThreshold lowerPrime upperPrime N H p₀ k m) :
    lengthCutoff ≤ H ∨
      ¬AvoidsSquareMultiplesAtLeast N H squareThreshold ∨
      ¬Nonempty (TypicalPrimeAnatomy lowerPrime upperPrime p₀ m) := by
  have hfail := hnon.2.2.2
  simp only [SatisfiesTypicalNormalizedConditions, not_and_or] at hfail
  rcases hfail with hlength | hsquare | hanatomy
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl hsquare)
  · exact Or.inr (Or.inr hanatomy)

theorem IsTypicalScaleNormalizedBadInterval.length_lt
    {x lengthCutoff squareThreshold lowerPrime upperPrime
      N H p₀ k m : ℕ}
    (htyp : IsTypicalScaleNormalizedBadInterval x lengthCutoff
      squareThreshold lowerPrime upperPrime N H p₀ k m) :
    H < lengthCutoff :=
  htyp.2.2.2.1

theorem IsTypicalScaleNormalizedBadInterval.avoidsSquareMultiples
    {x lengthCutoff squareThreshold lowerPrime upperPrime
      N H p₀ k m : ℕ}
    (htyp : IsTypicalScaleNormalizedBadInterval x lengthCutoff
      squareThreshold lowerPrime upperPrime N H p₀ k m) :
    AvoidsSquareMultiplesAtLeast N H squareThreshold :=
  htyp.2.2.2.2.1

/-- Condition (ii), applied to the distinguished value `p₀²m`, forces
`p₀` below the square threshold.  This is the exact step yielding `p₀ < z³`
in the proof of Proposition 6.5. -/
theorem IsTypicalScaleNormalizedBadInterval.p₀_lt_squareThreshold
    {x lengthCutoff squareThreshold lowerPrime upperPrime
      N H p₀ k m : ℕ}
    (htyp : IsTypicalScaleNormalizedBadInterval x lengthCutoff
      squareThreshold lowerPrime upperPrime N H p₀ k m) :
    p₀ < squareThreshold := by
  obtain ⟨_hH, _hbad, _hp, _hHltp, _hpMax, hk, _hmSmooth, hkm,
    _hkEndpoint, _hpow⟩ := htyp.1
  by_contra hnot
  have hthreshold : squareThreshold ≤ p₀ := by omega
  have hpSq : p₀ ^ 2 ∣ k := by
    rw [hkm]
    exact dvd_mul_right (p₀ ^ 2) m
  exact htyp.avoidsSquareMultiples k hk p₀ hthreshold hpSq

theorem TypicalPrimeAnatomy.lower_le_factor
    {lowerPrime upperPrime p₀ m : ℕ}
    (a : TypicalPrimeAnatomy lowerPrime upperPrime p₀ m)
    (i : Fin 1000) : lowerPrime ≤ a.factors i := by
  exact a.lower_le_last.trans
    (a.factors_nonincreasing (Fin.le_last i))

theorem TypicalPrimeAnatomy.factor_le_p₀
    {lowerPrime upperPrime p₀ m : ℕ}
    (a : TypicalPrimeAnatomy lowerPrime upperPrime p₀ m)
    (i : Fin 1000) : a.factors i ≤ p₀ := by
  exact (a.factors_nonincreasing (Fin.zero_le i)).trans a.first_le_p₀

theorem TypicalPrimeAnatomy.lower_le_p₀
    {lowerPrime upperPrime p₀ m : ℕ}
    (a : TypicalPrimeAnatomy lowerPrime upperPrime p₀ m) :
    lowerPrime ≤ p₀ :=
  (a.lower_le_factor 0).trans a.first_le_p₀

theorem TypicalPrimeAnatomy.factor_le_upper
    {lowerPrime upperPrime p₀ m : ℕ}
    (a : TypicalPrimeAnatomy lowerPrime upperPrime p₀ m)
    (i : Fin 1000) : a.factors i ≤ upperPrime :=
  (a.factor_le_p₀ i).trans a.p₀_le_upper

/-- The selected product of 1000 primes divides the smooth cofactor `m`. -/
theorem TypicalPrimeAnatomy.factorProduct_dvd
    {lowerPrime upperPrime p₀ m : ℕ}
    (a : TypicalPrimeAnatomy lowerPrime upperPrime p₀ m) :
    (∏ i, a.factors i) ∣ m := by
  exact ⟨a.remainder, a.factorization⟩

theorem TypicalPrimeAnatomy.factorProduct_pos
    {lowerPrime upperPrime p₀ m : ℕ}
    (a : TypicalPrimeAnatomy lowerPrime upperPrime p₀ m) :
    0 < ∏ i, a.factors i := by
  exact Finset.prod_pos fun i _hi => (a.factors_prime i).pos

/-- Exact division-form consequence displayed after Definition 6.4 in the
source: `m' ≤ 2x/(p₀² p₁...p₁₀₀₀)`. -/
theorem IsTypicalScaleNormalizedBadInterval.exists_anatomy_with_remainder_bound
    {x lengthCutoff squareThreshold lowerPrime upperPrime
      N H p₀ k m : ℕ}
    (htyp : IsTypicalScaleNormalizedBadInterval x lengthCutoff
      squareThreshold lowerPrime upperPrime N H p₀ k m) :
    ∃ a : TypicalPrimeAnatomy lowerPrime upperPrime p₀ m,
      a.remainder ≤ 2 * x / (p₀ ^ 2 * ∏ i, a.factors i) := by
  obtain ⟨a⟩ := htyp.2.2.2.2.2
  refine ⟨a, ?_⟩
  obtain ⟨_hH, _hbad, hp₀, _hHltp, _hpMax, hk, _hmSmooth, hkm,
    _hkEndpoint, _hpow⟩ := htyp.1
  have hkUpper : k ≤ N + H := (Finset.mem_Ioc.mp hk).2
  have hkTwoX : k ≤ 2 * x := hkUpper.trans htyp.2.2.1
  have hkEq :
      k = (p₀ ^ 2 * ∏ i, a.factors i) * a.remainder := by
    calc
      k = p₀ ^ 2 * m := hkm
      _ = p₀ ^ 2 * ((∏ i, a.factors i) * a.remainder) :=
        congrArg (fun t => p₀ ^ 2 * t) a.factorization
      _ = (p₀ ^ 2 * ∏ i, a.factors i) * a.remainder := by
        rw [Nat.mul_assoc]
  have hmul :
      (p₀ ^ 2 * ∏ i, a.factors i) * a.remainder ≤ 2 * x := by
    rw [← hkEq]
    exact hkTwoX
  have hdenom : 0 < p₀ ^ 2 * ∏ i, a.factors i :=
    Nat.mul_pos (pow_pos hp₀.pos 2) a.factorProduct_pos
  rw [Nat.le_div_iff_mul_le hdenom]
  simpa only [Nat.mul_comm] using hmul

end Tao2026
