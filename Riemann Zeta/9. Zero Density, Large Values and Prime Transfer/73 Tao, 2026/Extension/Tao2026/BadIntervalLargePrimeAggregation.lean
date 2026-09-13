import Tao2026.BadIntervalLargePrimeProbabilityBounds
import Tao2026.BadIntervalLargePrimePairs

/-!
# Finite large-prime mean and covariance aggregation

This module performs the exact finite partition used after Propositions 6.7
and 6.8.  A single prime is charged either to the improved marginal estimate
or to a supplied crude exceptional estimate.  Likewise, every ordered pair of
distinct primes is charged either to the improved covariance error or to a
supplied crude joint estimate.  The statements use the literal anti-sieve
index set, so all multiplicities in the shift variables remain visible.
-/

namespace Tao2026

open scoped Classical

noncomputable section

set_option maxRecDepth 10000

/-- The complete error occurring after cancellation of the distinct-prime
covariance main terms. -/
def taoLargePrimeCovarianceImprovedError
    (P : Fin 1001 → ℕ) (p q : ℕ) : ℝ :=
  taoLargePrimeJointImprovedError P p q +
    (1 / (p.totient : ℝ)) * taoLargePrimeImprovedError P q +
    (1 / (q.totient : ℝ)) * taoLargePrimeImprovedError P p +
    taoLargePrimeImprovedError P p * taoLargePrimeImprovedError P q

/-- A pair is unexceptional precisely when none of the three possible
nontrivial conductors `p`, `q`, and `pq` (expressed invariantly as divisors of
`pq`) is exceptional at any ordinary tuple-coordinate scale. -/
def TaoLargePrimePairUnexceptional
    (P : Fin 1001 → ℕ) (a b : ℕ × ℕ) : Prop :=
  ∀ d ∈ (a.2 * b.2).divisors.erase 1,
    d ∉ taoLargePrimeExceptionalConductorsFor
      ((a.2 * b.2).divisors.erase 1) P

theorem taoLargePrimeCovariance_le_jointProbability
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (m' : ℕ) (a b : ℕ × ℕ) :
    taoLargePrimeCovariance P hP m' a b ≤
      taoLargePrimeJointProbability P hP m' a b := by
  unfold taoLargePrimeCovariance
  have ha := taoLargePrimeProbability_nonneg P hP m' a
  have hb := taoLargePrimeProbability_nonneg P hP m' b
  nlinarith [mul_nonneg ha hb]

/-- Exact finite Proposition 6.7 partition on the literal anti-sieve index
set.  Exceptional conductors use the supplied pointwise crude majorant `B`;
all other conductors use the proved main term plus improved error. -/
theorem sum_taoLargePrimeProbability_le_exceptionalPartition
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (lowerPrime upperPrime H m' : ℕ) (hH : H ≤ lowerPrime)
    (hm : ∀ p ∈ taoLargeAntiSievePrimeRange lowerPrime upperPrime,
      Nat.Coprime m' p)
    (B : ℕ × ℕ → ℝ)
    (hB : ∀ a ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H,
      a.2 ∈ taoLargePrimeExceptionalConductorsFor
        (taoLargeAntiSievePrimeRange lowerPrime upperPrime) P →
      taoLargePrimeProbability P hP m' a ≤ B a) :
    (∑ a ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H,
      taoLargePrimeProbability P hP m' a) ≤
      ∑ a ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H,
        if a.2 ∈ taoLargePrimeExceptionalConductorsFor
            (taoLargeAntiSievePrimeRange lowerPrime upperPrime) P then
          B a
        else
          1 / (a.2.totient : ℝ) + taoLargePrimeImprovedError P a.2 := by
  apply Finset.sum_le_sum
  intro a ha
  by_cases haExceptional : a.2 ∈ taoLargePrimeExceptionalConductorsFor
      (taoLargeAntiSievePrimeRange lowerPrime upperPrime) P
  · rw [if_pos haExceptional]
    exact hB a ha haExceptional
  · rw [if_neg haExceptional]
    have haData := mem_taoLargeAntiSieveIndices.mp ha
    have hpD : a.2 ∈ taoLargeAntiSievePrimeRange lowerPrime upperPrime :=
      mem_taoLargeAntiSievePrimeRange.mpr
        ⟨haData.2.2.1, haData.2.2.2.1, haData.2.2.2.2⟩
    have halp : a.1 < a.2 :=
      lt_of_lt_of_le haData.2.1
        (le_trans hH (Nat.le_of_lt haData.2.2.2.1))
    have hpa : ¬a.2 ∣ a.1 :=
      Nat.not_dvd_of_pos_of_lt haData.1 halp
    exact taoLargePrimeProbability_le_main_add_unexceptionalError
      a haData.2.2.1 hpD hpa (hm a.2 hpD) P hP haExceptional

/-- Exact finite Proposition 6.8 partition of the ordered distinct-prime
covariance sum.  An unexceptional pair uses the proved covariance error;
every remaining pair is bounded by a supplied crude joint majorant `B`. -/
theorem sum_taoLargePrimeCovariance_le_exceptionalPairPartition
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (lowerPrime upperPrime H m' : ℕ) (hH : H ≤ lowerPrime)
    (hm : ∀ p ∈ taoLargeAntiSievePrimeRange lowerPrime upperPrime,
      Nat.Coprime m' p)
    (B : (ℕ × ℕ) → (ℕ × ℕ) → ℝ)
    (hB : ∀ a ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H,
      ∀ b ∈ (taoLargeAntiSieveIndices lowerPrime upperPrime H).filter
        (fun b => b.2 ≠ a.2),
      ¬TaoLargePrimePairUnexceptional P a b →
      taoLargePrimeJointProbability P hP m' a b ≤ B a b) :
    (∑ a ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H,
      ∑ b ∈ (taoLargeAntiSieveIndices lowerPrime upperPrime H).filter
        (fun b => b.2 ≠ a.2), taoLargePrimeCovariance P hP m' a b) ≤
      ∑ a ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H,
        ∑ b ∈ (taoLargeAntiSieveIndices lowerPrime upperPrime H).filter
          (fun b => b.2 ≠ a.2),
          if TaoLargePrimePairUnexceptional P a b then
            taoLargePrimeCovarianceImprovedError P a.2 b.2
          else B a b := by
  apply Finset.sum_le_sum
  intro a ha
  apply Finset.sum_le_sum
  intro b hb
  have haData := mem_taoLargeAntiSieveIndices.mp ha
  have hbMem := (Finset.mem_filter.mp hb).1
  have hpq : a.2 ≠ b.2 := (Finset.mem_filter.mp hb).2.symm
  have hbData := mem_taoLargeAntiSieveIndices.mp hbMem
  by_cases habExceptional : TaoLargePrimePairUnexceptional P a b
  · rw [if_pos habExceptional]
    have haPrimeMem : a.2 ∈ taoLargeAntiSievePrimeRange lowerPrime upperPrime :=
      mem_taoLargeAntiSievePrimeRange.mpr
        ⟨haData.2.2.1, haData.2.2.2.1, haData.2.2.2.2⟩
    have hbPrimeMem : b.2 ∈ taoLargeAntiSievePrimeRange lowerPrime upperPrime :=
      mem_taoLargeAntiSievePrimeRange.mpr
        ⟨hbData.2.2.1, hbData.2.2.2.1, hbData.2.2.2.2⟩
    have halp : a.1 < a.2 :=
      lt_of_lt_of_le haData.2.1
        (le_trans hH (Nat.le_of_lt haData.2.2.2.1))
    have hblq : b.1 < b.2 :=
      lt_of_lt_of_le hbData.2.1
        (le_trans hH (Nat.le_of_lt hbData.2.2.2.1))
    have hpa : ¬a.2 ∣ a.1 := Nat.not_dvd_of_pos_of_lt haData.1 halp
    have hqb : ¬b.2 ∣ b.1 := Nat.not_dvd_of_pos_of_lt hbData.1 hblq
    have hmPair : Nat.Coprime m' (a.2 * b.2) :=
      Nat.coprime_mul_iff_right.mpr
        ⟨hm a.2 haPrimeMem, hm b.2 hbPrimeMem⟩
    simpa only [taoLargePrimeCovarianceImprovedError] using
      taoLargePrimeCovariance_le_unexceptionalErrors
        a b haData.2.2.1 hbData.2.2.1 hpq hpa hqb hmPair P hP
          habExceptional
  · rw [if_neg habExceptional]
    exact (taoLargePrimeCovariance_le_jointProbability P hP m' a b).trans
      (hB a ha b hb habExceptional)

/-- Source-facing finite variance aggregation.  It combines the diagonal
reduction with the exact exceptional partitions for the mean and the ordered
distinct-prime covariance sum. -/
theorem taoLargePrimeVariance_le_exceptionalPartitions
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (lowerPrime upperPrime H m' : ℕ) (hH : H ≤ lowerPrime)
    (hm : ∀ p ∈ taoLargeAntiSievePrimeRange lowerPrime upperPrime,
      Nat.Coprime m' p)
    (B₁ : ℕ × ℕ → ℝ) (B₂ : (ℕ × ℕ) → (ℕ × ℕ) → ℝ)
    (hB₁ : ∀ a ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H,
      a.2 ∈ taoLargePrimeExceptionalConductorsFor
        (taoLargeAntiSievePrimeRange lowerPrime upperPrime) P →
      taoLargePrimeProbability P hP m' a ≤ B₁ a)
    (hB₂ : ∀ a ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H,
      ∀ b ∈ (taoLargeAntiSieveIndices lowerPrime upperPrime H).filter
        (fun b => b.2 ≠ a.2),
      ¬TaoLargePrimePairUnexceptional P a b →
      taoLargePrimeJointProbability P hP m' a b ≤ B₂ a b) :
    taoLargePrimeVariance P hP lowerPrime upperPrime H m' ≤
      (∑ a ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H,
        if a.2 ∈ taoLargePrimeExceptionalConductorsFor
            (taoLargeAntiSievePrimeRange lowerPrime upperPrime) P then
          B₁ a
        else
          1 / (a.2.totient : ℝ) + taoLargePrimeImprovedError P a.2) +
      ∑ a ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H,
        ∑ b ∈ (taoLargeAntiSieveIndices lowerPrime upperPrime H).filter
          (fun b => b.2 ≠ a.2),
          if TaoLargePrimePairUnexceptional P a b then
            taoLargePrimeCovarianceImprovedError P a.2 b.2
          else B₂ a b := by
  refine (taoLargePrimeVariance_le_mean_add_distinctPrimeCovariances
    P hP lowerPrime upperPrime H m' hH).trans ?_
  apply add_le_add
  · rw [taoLargePrimeMean_eq]
    exact sum_taoLargePrimeProbability_le_exceptionalPartition
      P hP lowerPrime upperPrime H m' hH hm B₁ hB₁
  · exact sum_taoLargePrimeCovariance_le_exceptionalPairPartition
      P hP lowerPrime upperPrime H m' hH hm B₂ hB₂

end

end Tao2026
