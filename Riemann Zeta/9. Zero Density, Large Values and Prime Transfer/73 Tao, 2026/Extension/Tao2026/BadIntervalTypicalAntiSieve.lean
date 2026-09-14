import Tao2026.BadIntervalProbabilityNormalization

/-!
# Deterministic typical-interval bridge for Proposition 6.6

This module connects typical normalized intervals to the three probabilistic
large-deviation branches.  It first develops the exact logarithmic
squarefree-factor and weighted large-prime bookkeeping used by the source
anti-sieve.
-/

namespace Tao2026

open Filter Topology MeasureTheory
open scoped Classical BigOperators

noncomputable section

/-- Logarithmically weighted version of the large-prime divisibility
contribution. -/
def taoLargePrimeLogContribution
    (lowerPrime upperPrime H m' : ℕ) (ω : TaoPrimeTuple) : ℝ :=
  ∑ lp ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H,
    taoPrimeDivisibilityIndicator m' lp.1 lp.2 ω * Real.log lp.2

theorem taoLargePrimeLogContribution_nonneg
    (lowerPrime upperPrime H m' : ℕ) (ω : TaoPrimeTuple) :
    0 ≤ taoLargePrimeLogContribution lowerPrime upperPrime H m' ω := by
  apply Finset.sum_nonneg
  intro lp hlp
  have hpPrime := (mem_taoLargeAntiSieveIndices.mp hlp).2.2.1
  exact mul_nonneg (taoPrimeDivisibilityIndicator_nonneg _ _ _ _)
    (Real.log_nonneg (by exact_mod_cast hpPrime.one_le))

/-- On a finite large-prime range, logarithmic weighting costs at most the
logarithm of the upper endpoint. -/
theorem taoLargePrimeLogContribution_le_log_mul
    (lowerPrime upperPrime H m' : ℕ) (ω : TaoPrimeTuple) :
    taoLargePrimeLogContribution lowerPrime upperPrime H m' ω ≤
      Real.log upperPrime *
        taoLargePrimeContribution lowerPrime upperPrime H m' ω := by
  unfold taoLargePrimeLogContribution taoLargePrimeContribution
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro lp hlp
  have hpData := mem_taoLargeAntiSieveIndices.mp hlp
  have hpPrime : Nat.Prime lp.2 := hpData.2.2.1
  have hpUpper : lp.2 ≤ upperPrime := hpData.2.2.2.2
  have hlog : Real.log (lp.2 : ℝ) ≤ Real.log (upperPrime : ℝ) :=
    Real.log_le_log (by exact_mod_cast hpPrime.pos)
      (by exact_mod_cast hpUpper)
  calc
    taoPrimeDivisibilityIndicator m' lp.1 lp.2 ω * Real.log lp.2 ≤
        taoPrimeDivisibilityIndicator m' lp.1 lp.2 ω * Real.log upperPrime :=
      mul_le_mul_of_nonneg_left hlog
        (taoPrimeDivisibilityIndicator_nonneg _ _ _ _)
    _ = Real.log upperPrime *
        taoPrimeDivisibilityIndicator m' lp.1 lp.2 ω := by ring

/-- The logarithm of the squarefree component is exactly the sum of the
logarithms of its prime factors. -/
theorem sum_log_primeFactors_squarefreeComponent_eq
    {n : ℕ} (hn : 0 < n) :
    (∑ p ∈ (squarefreeComponent n).primeFactors, Real.log p) =
      Real.log (squarefreeComponent n) := by
  obtain ⟨a, ha⟩ := exists_sq_mul_squarefreeComponent hn
  have hcomponentPos : 0 < squarefreeComponent n := by
    by_contra h
    have hz : squarefreeComponent n = 0 := Nat.eq_zero_of_not_pos h
    rw [hz, mul_zero] at ha
    omega
  have hnonzero : ∀ p ∈ (squarefreeComponent n).primeFactors,
      (p : ℝ) ≠ 0 := by
    intro p hp
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
  calc
    (∑ p ∈ (squarefreeComponent n).primeFactors, Real.log p) =
        Real.log
          (∏ p ∈ (squarefreeComponent n).primeFactors, (p : ℝ)) := by
      symm
      exact Real.log_prod hnonzero
    _ = Real.log
        ((∏ p ∈ (squarefreeComponent n).primeFactors, p : ℕ) : ℝ) := by
      push_cast
      rfl
    _ = Real.log (squarefreeComponent n) := by
      rw [Nat.prod_primeFactors_of_squarefree
        (squarefree_squarefreeComponent n)]

/-! ## Shiftwise prime-factor partition -/

/-- Small-prime logarithmic contribution at one fixed shift. -/
def taoSmallPrimeContributionAtShift
    (x l m' : ℕ) (ω : TaoPrimeTuple) : ℝ :=
  ∑ p ∈ (taoSmallAntiSievePrimeRange x).filter (fun p => ¬p ∣ l),
    taoPrimeDivisibilityIndicator m' l p ω * Real.log p

/-- Large-prime logarithmic contribution at one fixed shift. -/
def taoLargePrimeLogContributionAtShift
    (lowerPrime upperPrime l m' : ℕ) (ω : TaoPrimeTuple) : ℝ :=
  ∑ p ∈ taoLargeAntiSievePrimeRange lowerPrime upperPrime,
    taoPrimeDivisibilityIndicator m' l p ω * Real.log p

theorem sum_taoSmallPrimeContributionAtShift_eq
    (x H m' : ℕ) (ω : TaoPrimeTuple) :
    (∑ l ∈ Finset.Ico 1 H,
        taoSmallPrimeContributionAtShift x l m' ω) =
      taoSmallPrimeContribution x H m' ω := by
  unfold taoSmallPrimeContributionAtShift taoSmallPrimeContribution
    taoSmallAntiSieveTerm taoSmallAntiSieveIndices
  rw [show
      (∑ lp ∈ ((Finset.Ico 1 H).product
          (taoSmallAntiSievePrimeRange x)).filter (fun lp => ¬lp.2 ∣ lp.1),
        taoPrimeDivisibilityIndicator m' lp.1 lp.2 ω * Real.log lp.2) =
        ∑ l ∈ Finset.Ico 1 H,
          ∑ p ∈ (taoSmallAntiSievePrimeRange x).filter (fun p => ¬p ∣ l),
            taoPrimeDivisibilityIndicator m' l p ω * Real.log p by
    rw [Finset.sum_filter]
    simp_rw [Finset.sum_filter]
    exact Finset.sum_product _ _ _]

theorem sum_taoLargePrimeLogContributionAtShift_eq
    (lowerPrime upperPrime H m' : ℕ) (ω : TaoPrimeTuple) :
    (∑ l ∈ Finset.Ico 1 H,
        taoLargePrimeLogContributionAtShift lowerPrime upperPrime l m' ω) =
      taoLargePrimeLogContribution lowerPrime upperPrime H m' ω := by
  unfold taoLargePrimeLogContributionAtShift taoLargePrimeLogContribution
    taoLargeAntiSieveIndices
  exact (Finset.sum_product (Finset.Ico 1 H)
    (taoLargeAntiSievePrimeRange lowerPrime upperPrime)
    (fun lp : ℕ × ℕ =>
      taoPrimeDivisibilityIndicator m' lp.1 lp.2 ω * Real.log lp.2)).symm

/-- At one positive shift, every prime in the squarefree component belongs
to the exceptional, small, or large anti-sieve range. -/
theorem sum_log_primeFactors_squarefreeComponent_le_three_shift_contributions
    {x l upperPrime m' : ℕ} {ω : TaoPrimeTuple}
    (hl : 0 < l)
    (hsmooth : IsSmooth (taoPrimeTupleStart m' ω + l) upperPrime) :
    (∑ p ∈ (squarefreeComponent
          (taoPrimeTupleStart m' ω + l)).primeFactors, Real.log p) ≤
      taoExceptionalShiftPrimeWeight m' l ω +
        taoSmallPrimeContributionAtShift x l m' ω +
          taoLargePrimeLogContributionAtShift
            (taoSmallAntiSievePrimeCutoff x) upperPrime l m' ω := by
  let n : ℕ := taoPrimeTupleStart m' ω + l
  let F : Finset ℕ := (squarefreeComponent n).primeFactors
  let E : Finset ℕ := l.primeFactors
  let S : Finset ℕ :=
    (taoSmallAntiSievePrimeRange x).filter (fun p => ¬p ∣ l)
  let L : Finset ℕ :=
    taoLargeAntiSievePrimeRange (taoSmallAntiSievePrimeCutoff x) upperPrime
  let f : ℕ → ℝ := fun p =>
    if p.Prime then
      taoPrimeDivisibilityIndicator m' l p ω * Real.log p
    else 0
  have hn : 0 < n := by dsimp only [n]; omega
  have hsubset : F ⊆ (E ∪ S) ∪ L := by
    intro p hpF
    have hpPrime : Nat.Prime p := Nat.prime_of_mem_primeFactors hpF
    have hpComponentDvd : p ∣ squarefreeComponent n :=
      Nat.dvd_of_mem_primeFactors hpF
    have hpN : p ∣ n :=
      dvd_trans hpComponentDvd (squarefreeComponent_dvd n)
    have hpUpper : p ≤ upperPrime :=
      (isSmooth_iff.mp hsmooth).2 p hpPrime (by simpa only [n] using hpN)
    by_cases hpl : p ∣ l
    · have hpE : p ∈ E := by
        dsimp only [E]
        exact hpPrime.mem_primeFactors hpl (Nat.ne_of_gt hl)
      exact Finset.mem_union_left _ (Finset.mem_union_left _ hpE)
    · by_cases hpSmall : p ≤ taoSmallAntiSievePrimeCutoff x
      · have hpS : p ∈ S := by
          change p ∈ (taoSmallAntiSievePrimeRange x).filter (fun p => ¬p ∣ l)
          rw [Finset.mem_filter, mem_taoSmallAntiSievePrimeRange]
          exact ⟨⟨hpPrime, hpSmall⟩, hpl⟩
        exact Finset.mem_union_left _ (Finset.mem_union_right _ hpS)
      · have hpL : p ∈ L := by
          change p ∈ taoLargeAntiSievePrimeRange
            (taoSmallAntiSievePrimeCutoff x) upperPrime
          rw [mem_taoLargeAntiSievePrimeRange]
          exact ⟨hpPrime, Nat.lt_of_not_ge hpSmall, hpUpper⟩
        exact Finset.mem_union_right _ hpL
  have hfNonneg : ∀ p, 0 ≤ f p := by
    intro p
    by_cases hp : p.Prime
    · change 0 ≤ if p.Prime then
          taoPrimeDivisibilityIndicator m' l p ω * Real.log p else 0
      rw [if_pos hp]
      exact mul_nonneg (taoPrimeDivisibilityIndicator_nonneg _ _ _ _)
        (Real.log_nonneg (by exact_mod_cast hp.one_le))
    · simp [f, hp]
  have hfactorEq :
      (∑ p ∈ F, Real.log p) = ∑ p ∈ F, f p := by
    apply Finset.sum_congr rfl
    intro p hp
    have hpPrime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hpComponentDvd : p ∣ squarefreeComponent n :=
      Nat.dvd_of_mem_primeFactors hp
    have hpN : p ∣ taoPrimeTupleStart m' ω + l := by
      simpa only [n] using
        dvd_trans hpComponentDvd (squarefreeComponent_dvd n)
    simp [f, hpPrime, taoPrimeDivisibilityIndicator, hpN]
  have hEeq : (∑ p ∈ E, f p) =
      taoExceptionalShiftPrimeWeight m' l ω := by
    unfold taoExceptionalShiftPrimeWeight
    apply Finset.sum_congr rfl
    intro p hp
    have hpPrime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    simp [f, hpPrime]
  have hSeq : (∑ p ∈ S, f p) =
      taoSmallPrimeContributionAtShift x l m' ω := by
    unfold taoSmallPrimeContributionAtShift
    apply Finset.sum_congr rfl
    intro p hp
    have hpPrime : Nat.Prime p :=
      (mem_taoSmallAntiSievePrimeRange.mp (Finset.mem_filter.mp hp).1).1
    simp [f, hpPrime]
  have hLeq : (∑ p ∈ L, f p) =
      taoLargePrimeLogContributionAtShift
        (taoSmallAntiSievePrimeCutoff x) upperPrime l m' ω := by
    unfold taoLargePrimeLogContributionAtShift
    apply Finset.sum_congr rfl
    intro p hp
    have hpPrime : Nat.Prime p :=
      (mem_taoLargeAntiSievePrimeRange.mp hp).1
    simp [f, hpPrime]
  change (∑ p ∈ F, Real.log p) ≤ _
  calc
    (∑ p ∈ F, Real.log p) = ∑ p ∈ F, f p := hfactorEq
    _ ≤ ∑ p ∈ (E ∪ S) ∪ L, f p :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun p _ _ => hfNonneg p)
    _ ≤ (∑ p ∈ E ∪ S, f p) + ∑ p ∈ L, f p :=
      sum_union_le_add_sum_of_nonneg _ _ f hfNonneg
    _ ≤ ((∑ p ∈ E, f p) + ∑ p ∈ S, f p) + ∑ p ∈ L, f p := by
      gcongr
      exact sum_union_le_add_sum_of_nonneg _ _ f hfNonneg
    _ = taoExceptionalShiftPrimeWeight m' l ω +
        taoSmallPrimeContributionAtShift x l m' ω +
          taoLargePrimeLogContributionAtShift
            (taoSmallAntiSievePrimeCutoff x) upperPrime l m' ω := by
      rw [hEeq, hSeq, hLeq]

/-- Summing the shiftwise partition gives the three global anti-sieve
contributions with no loss. -/
theorem sum_squarefreePrimeLogs_le_three_contributions
    {x H upperPrime m' : ℕ} {ω : TaoPrimeTuple}
    (hsmooth : ∀ l ∈ Finset.Ico 1 H,
      IsSmooth (taoPrimeTupleStart m' ω + l) upperPrime) :
    (∑ l ∈ Finset.Ico 1 H,
        ∑ p ∈ (squarefreeComponent
          (taoPrimeTupleStart m' ω + l)).primeFactors, Real.log p) ≤
      taoExceptionalPrimeContribution H m' ω +
        taoSmallPrimeContribution x H m' ω +
          taoLargePrimeLogContribution
            (taoSmallAntiSievePrimeCutoff x) upperPrime H m' ω := by
  calc
    (∑ l ∈ Finset.Ico 1 H,
        ∑ p ∈ (squarefreeComponent
          (taoPrimeTupleStart m' ω + l)).primeFactors, Real.log p) ≤
      ∑ l ∈ Finset.Ico 1 H,
        (taoExceptionalShiftPrimeWeight m' l ω +
          taoSmallPrimeContributionAtShift x l m' ω +
            taoLargePrimeLogContributionAtShift
              (taoSmallAntiSievePrimeCutoff x) upperPrime l m' ω) := by
      apply Finset.sum_le_sum
      intro l hl
      exact sum_log_primeFactors_squarefreeComponent_le_three_shift_contributions
        (Finset.mem_Ico.mp hl).1 (hsmooth l hl)
    _ = taoExceptionalPrimeContribution H m' ω +
        taoSmallPrimeContribution x H m' ω +
          taoLargePrimeLogContribution
            (taoSmallAntiSievePrimeCutoff x) upperPrime H m' ω := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        sum_taoSmallPrimeContributionAtShift_eq,
        sum_taoLargePrimeLogContributionAtShift_eq]
      rfl

/-- Avoiding every square divisor with base at least `squareThreshold` forces
the squarefree component of each interval element to retain the logarithmic
size of that element, up to the exact factor `4 squareThreshold²`. -/
theorem log_squarefreeComponent_lower_of_avoids
    {x N H n squareThreshold : ℕ}
    (hx : 0 < x) (hthreshold : 0 < squareThreshold)
    (hleft : x ≤ 4 * N + 1)
    (hnmem : n ∈ consecutiveInterval N H)
    (havoid : AvoidsSquareMultiplesAtLeast N H squareThreshold) :
    Real.log x - Real.log 4 - 2 * Real.log squareThreshold ≤
      Real.log (squarefreeComponent n) := by
  have hn : 0 < n := by
    have hnData := Finset.mem_Ioc.mp hnmem
    omega
  obtain ⟨a, ha⟩ := exists_sq_mul_squarefreeComponent hn
  have haSqDvd : a ^ 2 ∣ n := by
    rw [← ha]
    exact dvd_mul_right _ _
  have haLt : a < squareThreshold := by
    by_contra h
    exact (havoid n hnmem a (Nat.le_of_not_gt h)) haSqDvd
  have haLe : a ≤ squareThreshold := haLt.le
  have hnLe : n ≤ squareThreshold ^ 2 * squarefreeComponent n := by
    calc
      n = a ^ 2 * squarefreeComponent n := ha.symm
      _ ≤ squareThreshold ^ 2 * squarefreeComponent n :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left haLe 2)
  have hxN : x ≤ 4 * n := by
    have hnData := Finset.mem_Ioc.mp hnmem
    omega
  have hbound : x ≤ 4 * (squareThreshold ^ 2 * squarefreeComponent n) :=
    hxN.trans (Nat.mul_le_mul_left 4 hnLe)
  have hcomponentPos : 0 < squarefreeComponent n := by
    by_contra h
    have hz : squarefreeComponent n = 0 := Nat.eq_zero_of_not_pos h
    rw [hz, mul_zero] at ha
    omega
  have hboundReal : (x : ℝ) ≤
      4 * ((squareThreshold : ℝ) ^ (2 : ℕ) * squarefreeComponent n) := by
    exact_mod_cast hbound
  have hlogBound : Real.log (x : ℝ) ≤
      Real.log
        (4 * ((squareThreshold : ℝ) ^ (2 : ℕ) * squarefreeComponent n)) :=
    Real.log_le_log (by exact_mod_cast hx) hboundReal
  calc
    Real.log x - Real.log 4 - 2 * Real.log squareThreshold ≤
        Real.log
          (4 * ((squareThreshold : ℝ) ^ (2 : ℕ) * squarefreeComponent n)) -
            Real.log 4 - 2 * Real.log squareThreshold := by linarith
    _ = Real.log (squarefreeComponent n) := by
      rw [Real.log_mul (by positivity)
        (mul_ne_zero (pow_ne_zero 2 (by exact_mod_cast hthreshold.ne'))
          (by exact_mod_cast hcomponentPos.ne')),
        Real.log_mul (pow_ne_zero 2 (by exact_mod_cast hthreshold.ne'))
          (by exact_mod_cast hcomponentPos.ne'),
        Real.log_pow]
      ring

/-- A typical tuple supplies the preceding squarefree logarithmic lower bound
at every nonzero shift. -/
theorem TaoPrimeTupleTypicalEvent.sum_squarefreePrimeLogs_lower
    {x H lowerPrime upperPrime m' : ℕ} {ω : TaoPrimeTuple}
    (hx : 0 < x)
    (htypical : TaoPrimeTupleTypicalEvent
      x H lowerPrime upperPrime m' ω) :
    ((H - 1 : ℕ) : ℝ) *
        (Real.log x - Real.log 4 -
          2 * Real.log (taoTypicalSquareThreshold x)) ≤
      ∑ l ∈ Finset.Ico 1 H,
        ∑ p ∈ (squarefreeComponent
          (taoPrimeTupleStart m' ω + l)).primeFactors, Real.log p := by
  rw [TaoPrimeTupleTypicalEvent,
    IsForwardTypicalScaleNormalizedBadInterval,
    IsTypicalScaleNormalizedBadInterval,
    SatisfiesTypicalNormalizedConditions] at htypical
  obtain ⟨⟨hnorm, hleft, _hright, _hlength, havoid, _hanatomy⟩,
    hstart⟩ := htypical
  have hpoint : ∀ l ∈ Finset.Ico 1 H,
      Real.log x - Real.log 4 -
          2 * Real.log (taoTypicalSquareThreshold x) ≤
        ∑ p ∈ (squarefreeComponent
          (taoPrimeTupleStart m' ω + l)).primeFactors, Real.log p := by
    intro l hl
    have hlData := Finset.mem_Ico.mp hl
    have hnmem : taoPrimeTupleStart m' ω + l ∈
        consecutiveInterval (taoPrimeTupleStart m' ω - 1) H := by
      rw [consecutiveInterval, Finset.mem_Ioc]
      omega
    calc
      Real.log x - Real.log 4 -
          2 * Real.log (taoTypicalSquareThreshold x) ≤
        Real.log (squarefreeComponent
          (taoPrimeTupleStart m' ω + l)) :=
        log_squarefreeComponent_lower_of_avoids hx
          (taoTypicalSquareThreshold_pos x) hleft hnmem havoid
      _ = ∑ p ∈ (squarefreeComponent
          (taoPrimeTupleStart m' ω + l)).primeFactors, Real.log p :=
        (sum_log_primeFactors_squarefreeComponent_eq (by omega)).symm
  calc
    ((H - 1 : ℕ) : ℝ) *
        (Real.log x - Real.log 4 -
          2 * Real.log (taoTypicalSquareThreshold x)) =
      ∑ _l ∈ Finset.Ico 1 H,
        (Real.log x - Real.log 4 -
          2 * Real.log (taoTypicalSquareThreshold x)) := by
      simp [Nat.card_Ico]
      ring
    _ ≤ ∑ l ∈ Finset.Ico 1 H,
        ∑ p ∈ (squarefreeComponent
          (taoPrimeTupleStart m' ω + l)).primeFactors, Real.log p := by
      exact Finset.sum_le_sum hpoint

/-- Typical anatomy bounds every prime factor of every shifted interval
element by the declared upper prime cutoff, so the global three-way
partition applies. -/
theorem TaoPrimeTupleTypicalEvent.sum_squarefreePrimeLogs_le_three_contributions
    {x H lowerPrime upperPrime m' : ℕ} {ω : TaoPrimeTuple}
    (htypical : TaoPrimeTupleTypicalEvent
      x H lowerPrime upperPrime m' ω) :
    (∑ l ∈ Finset.Ico 1 H,
        ∑ p ∈ (squarefreeComponent
          (taoPrimeTupleStart m' ω + l)).primeFactors, Real.log p) ≤
      taoExceptionalPrimeContribution H m' ω +
        taoSmallPrimeContribution x H m' ω +
          taoLargePrimeLogContribution
            (taoSmallAntiSievePrimeCutoff x) upperPrime H m' ω := by
  rw [TaoPrimeTupleTypicalEvent,
    IsForwardTypicalScaleNormalizedBadInterval,
    IsTypicalScaleNormalizedBadInterval,
    SatisfiesTypicalNormalizedConditions] at htypical
  obtain ⟨⟨hnorm, _hleft, _hright, _hlength, _havoid, hanatomy⟩,
    hstart⟩ := htypical
  let anatomy : TypicalPrimeAnatomy lowerPrime upperPrime (ω 0)
      (taoPrimeTupleTailProduct ω * m') := Classical.choice hanatomy
  have hpUpper : ω 0 ≤ upperPrime := anatomy.p₀_le_upper
  apply Tao2026.sum_squarefreePrimeLogs_le_three_contributions
  intro l hl
  have hlData := Finset.mem_Ico.mp hl
  have hnmem : taoPrimeTupleStart m' ω + l ∈
      consecutiveInterval (taoPrimeTupleStart m' ω - 1) H := by
    rw [consecutiveInterval, Finset.mem_Ioc]
    omega
  have hsmooth := hnorm.isSmooth_of_mem hnmem
  rw [isSmooth_iff] at hsmooth ⊢
  exact ⟨hsmooth.1, fun p hp hpdiv =>
    (hsmooth.2 p hp hpdiv).trans hpUpper⟩

/-- Deterministic anti-sieve inequality supplied by a typical tuple.  The
large-prime branch is expressed using the unweighted random variable already
controlled by the source mean and variance estimates. -/
theorem TaoPrimeTupleTypicalEvent.three_contributions_lower
    {x H lowerPrime upperPrime m' : ℕ} {ω : TaoPrimeTuple}
    (hx : 0 < x)
    (htypical : TaoPrimeTupleTypicalEvent
      x H lowerPrime upperPrime m' ω) :
    ((H - 1 : ℕ) : ℝ) *
        (Real.log x - Real.log 4 -
          2 * Real.log (taoTypicalSquareThreshold x)) ≤
      taoExceptionalPrimeContribution H m' ω +
        taoSmallPrimeContribution x H m' ω +
          Real.log upperPrime *
            taoLargePrimeContribution
              (taoSmallAntiSievePrimeCutoff x) upperPrime H m' ω := by
  calc
    ((H - 1 : ℕ) : ℝ) *
        (Real.log x - Real.log 4 -
          2 * Real.log (taoTypicalSquareThreshold x)) ≤
      ∑ l ∈ Finset.Ico 1 H,
        ∑ p ∈ (squarefreeComponent
          (taoPrimeTupleStart m' ω + l)).primeFactors, Real.log p :=
      htypical.sum_squarefreePrimeLogs_lower hx
    _ ≤ taoExceptionalPrimeContribution H m' ω +
        taoSmallPrimeContribution x H m' ω +
          taoLargePrimeLogContribution
            (taoSmallAntiSievePrimeCutoff x) upperPrime H m' ω :=
      htypical.sum_squarefreePrimeLogs_le_three_contributions
    _ ≤ taoExceptionalPrimeContribution H m' ω +
        taoSmallPrimeContribution x H m' ω +
          Real.log upperPrime *
            taoLargePrimeContribution
              (taoSmallAntiSievePrimeCutoff x) upperPrime H m' ω := by
      gcongr
      exact taoLargePrimeLogContribution_le_log_mul
        (taoSmallAntiSievePrimeCutoff x) upperPrime H m' ω

/-! ## Source-scale scalar margin -/

/-- Exact identity underlying the notation `log x = log^(2-o(1)) z`. -/
theorem log_nat_eq_two_mul_log_taoZ_sq_div_iteratedLog
    {x : ℕ} (hlog : 0 < Real.log x) (hiter : 0 < iteratedLog x) :
    Real.log x =
      2 * Real.log (taoZ x) ^ (2 : ℕ) / iteratedLog x := by
  have hlogZ : 0 < Real.log (taoZ x) := by
    rw [log_taoZ]
    positivity
  have hxRatio := log_div_log_taoZ_eq_taoUZero hlog hiter
  have huRatio := taoUZero_div_log_taoZ_eq hlog hiter
  rw [div_eq_iff hlogZ.ne'] at hxRatio huRatio
  rw [huRatio] at hxRatio
  calc
    Real.log x = (2 / iteratedLog x * Real.log (taoZ x)) *
        Real.log (taoZ x) := hxRatio
    _ = 2 * Real.log (taoZ x) ^ (2 : ℕ) / iteratedLog x := by
      field_simp [hiter.ne']

/-- The ceiling in the typical square cutoff costs only a factor two before
taking logarithms. -/
theorem log_taoTypicalSquareThreshold_le (x : ℕ) :
    Real.log (taoTypicalSquareThreshold x : ℝ) ≤
      Real.log 2 + 3 * Real.log (taoZ x) := by
  have hzOne : (1 : ℝ) ≤ taoZ x := by
    rw [taoZ]
    exact Real.one_le_exp (by positivity)
  have hzPowOne : (1 : ℝ) ≤ (taoZ x) ^ (3 : ℕ) := one_le_pow₀ hzOne
  have hceil : (taoTypicalSquareThreshold x : ℝ) <
      (taoZ x) ^ (3 : ℕ) + 1 := by
    simpa only [taoTypicalSquareThreshold] using
      Nat.ceil_lt_add_one (pow_nonneg (taoZ_pos x).le 3)
  have hthresholdLe : (taoTypicalSquareThreshold x : ℝ) ≤
      2 * (taoZ x) ^ (3 : ℕ) := by linarith
  have hthresholdPos : (0 : ℝ) < taoTypicalSquareThreshold x := by
    exact_mod_cast taoTypicalSquareThreshold_pos x
  calc
    Real.log (taoTypicalSquareThreshold x : ℝ) ≤
        Real.log (2 * (taoZ x) ^ (3 : ℕ)) :=
      Real.log_le_log hthresholdPos hthresholdLe
    _ = Real.log 2 + 3 * Real.log (taoZ x) := by
      rw [Real.log_mul (by norm_num) (pow_ne_zero 3 (taoZ_pos x).ne'),
        Real.log_pow]
      norm_num

/-- The rounded upper endpoint of the literal large-prime range has the
expected logarithmic size. -/
theorem eventually_log_taoLargePrimeSourceUpperCutoff_le :
    ∀ᶠ x : ℕ in atTop,
      0 ≤ Real.log (taoLargePrimeSourceUpperCutoff x : ℝ) ∧
      Real.log (taoLargePrimeSourceUpperCutoff x : ℝ) ≤
        (101 / 100 : ℝ) * Real.log (taoZ x) := by
  filter_upwards [(tendsto_taoZPowerFloor_atTop
    (by norm_num : (0 : ℝ) < 101 / 100)).eventually
      (eventually_ge_atTop (1 : ℕ))] with x hupperPos
  have hupperFloor : (taoLargePrimeSourceUpperCutoff x : ℝ) ≤
      (taoZ x) ^ (101 / 100 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg (taoZ_pos x).le _)
  have hupperRealPos : (0 : ℝ) < taoLargePrimeSourceUpperCutoff x := by
    exact_mod_cast hupperPos
  constructor
  · exact Real.log_nonneg (by exact_mod_cast hupperPos)
  · calc
      Real.log (taoLargePrimeSourceUpperCutoff x : ℝ) ≤
          Real.log ((taoZ x) ^ (101 / 100 : ℝ)) :=
        Real.log_le_log hupperRealPos hupperFloor
      _ = (101 / 100 : ℝ) * Real.log (taoZ x) := by
        rw [Real.log_rpow (taoZ_pos x)]

/-- Eventually the squarefree logarithmic lower bound has ample room for all
three source anti-sieve thresholds, including the completed large-prime mean.
-/
theorem eventually_taoSourceAntiSieve_scalar_gap :
    ∀ᶠ x : ℕ in atTop,
      0 < iteratedLog x ∧
      1 ≤ Real.log (taoZ x) ∧
      0 ≤ Real.log (taoLargePrimeSourceUpperCutoff x : ℝ) ∧
      Real.log (taoZ x) +
          Real.log (taoZ x) ^ (2 : ℕ) / (8 * iteratedLog x) +
          Real.log (taoLargePrimeSourceUpperCutoff x : ℝ) *
            (2000000 + Real.log (taoZ x) / (8 * iteratedLog x)) <
        (1 / 2 : ℝ) *
          (Real.log x - Real.log 4 -
            2 * Real.log (taoTypicalSquareThreshold x : ℝ)) := by
  have hratio := tendsto_iteratedLog_div_log_taoZ_zero.eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 10000000))
  filter_upwards [hratio,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_gt_atTop (0 : ℝ)),
    tendsto_iteratedLog_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
    tendsto_taoZ_atTop.eventually (eventually_ge_atTop (Real.exp 1)),
    eventually_log_taoLargePrimeSourceUpperCutoff_le] with
      x hratioX hlogX hiterX hzX hupperX
  let L : ℝ := Real.log (taoZ x)
  let I : ℝ := iteratedLog x
  let R : ℝ := L ^ (2 : ℕ) / I
  let U : ℝ := Real.log (taoLargePrimeSourceUpperCutoff x : ℝ)
  have hLone : 1 ≤ L := by
    dsimp only [L]
    simpa only [Real.log_exp] using Real.log_le_log (by positivity) hzX
  have hLpos : 0 < L := zero_lt_one.trans_le hLone
  have hIpos : 0 < I := by simpa only [I] using hiterX
  have hratioLI : I / L < (1 / 10000000 : ℝ) := by
    simpa only [I, L] using hratioX
  have hIL : I < (1 / 10000000 : ℝ) * L :=
    (div_lt_iff₀ hLpos).mp hratioLI
  have hmul := mul_lt_mul_of_pos_right hIL hLpos
  have hRL : 10000000 * L < R := by
    dsimp only [R]
    rw [lt_div_iff₀ hIpos]
    nlinarith
  have hlogXeq : Real.log x = 2 * R := by
    simpa only [R, L, I, mul_div_assoc] using
      log_nat_eq_two_mul_log_taoZ_sq_div_iteratedLog hlogX hiterX
  have hlogTwo : Real.log (2 : ℝ) ≤ L := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h.trans hLone
  have hthreshold :
      Real.log (taoTypicalSquareThreshold x : ℝ) ≤ 4 * L := by
    calc
      Real.log (taoTypicalSquareThreshold x : ℝ) ≤
          Real.log 2 + 3 * Real.log (taoZ x) :=
        log_taoTypicalSquareThreshold_le x
      _ ≤ 4 * L := by
        dsimp only [L] at hlogTwo ⊢
        linarith
  have hlogFour : Real.log (4 : ℝ) ≤ 3 * L := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    norm_num at h
    nlinarith
  have hUdata : 0 ≤ U ∧ U ≤ (101 / 100 : ℝ) * L := by
    simpa only [U, L] using hupperX
  have hfactorNonneg :
      0 ≤ 2000000 + L / (8 * I) := by positivity
  have hupperBound :
      L + R / 8 + U * (2000000 + L / (8 * I)) ≤
        (201 / 800 : ℝ) * R + 2020001 * L := by
    calc
      L + R / 8 + U * (2000000 + L / (8 * I)) ≤
          L + R / 8 + ((101 / 100 : ℝ) * L) *
            (2000000 + L / (8 * I)) := by
        gcongr
        exact hUdata.2
      _ = (201 / 800 : ℝ) * R + 2020001 * L := by
        dsimp only [R]
        field_simp [hIpos.ne']
        ring
  have hlowerBound :
      R - (11 / 2 : ℝ) * L ≤
        (1 / 2 : ℝ) *
          (Real.log x - Real.log 4 -
            2 * Real.log (taoTypicalSquareThreshold x : ℝ)) := by
    rw [hlogXeq]
    nlinarith
  refine ⟨hiterX, hLone, hUdata.1, ?_⟩
  have hRdiv : L ^ (2 : ℕ) / (8 * I) = R / 8 := by
    dsimp only [R]
    field_simp [hIpos.ne']
  change L + L ^ (2 : ℕ) / (8 * I) +
      U * (2000000 + L / (8 * I)) < _
  rw [hRdiv]
  exact lt_of_le_of_lt hupperBound
    (lt_of_lt_of_le (by nlinarith [hRL]) hlowerBound)

/-! ## Typical-event inclusion and probability closure -/

/-- Every source-scale typical tuple eventually lies in one of the three
large-deviation events.  This is the deterministic anti-sieve implication at
the heart of Proposition 6.6. -/
theorem eventually_taoPrimeTupleTypicalEvent_imp_taoSourceAntiSieveLargeEvent :
    ∀ᶠ x : ℕ in atTop, ∀ H lowerPrime m' : ℕ, ∀ ω : TaoPrimeTuple,
      TaoPrimeTupleTypicalEvent x H lowerPrime
          (taoLargePrimeSourceUpperCutoff x) m' ω →
        TaoSourceAntiSieveLargeEvent x H m' ω := by
  filter_upwards [eventually_taoSourceAntiSieve_scalar_gap,
    eventually_gt_atTop (0 : ℕ)] with x hgap hx H lowerPrime m' ω htypical
  have htypicalData := htypical
  rw [TaoPrimeTupleTypicalEvent,
    IsForwardTypicalScaleNormalizedBadInterval,
    IsTypicalScaleNormalizedBadInterval,
    SatisfiesTypicalNormalizedConditions] at htypicalData
  obtain ⟨⟨hnorm, _hleft, _hright, _hlength, _havoid, _hanatomy⟩,
    _hstart⟩ := htypicalData
  have hHtwo : 2 ≤ H := hnorm.1
  have hHrealPos : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
  let L : ℝ := Real.log (taoZ x)
  let I : ℝ := iteratedLog x
  let R : ℝ := L ^ (2 : ℕ) / I
  let U : ℝ := Real.log (taoLargePrimeSourceUpperCutoff x : ℝ)
  let B : ℝ := Real.log x - Real.log 4 -
    2 * Real.log (taoTypicalSquareThreshold x : ℝ)
  let E : ℝ := taoExceptionalPrimeContribution H m' ω
  let S : ℝ := taoSmallPrimeContribution x H m' ω
  let X : ℝ := taoLargePrimeContribution
    (taoLargePrimeSourceLowerCutoff x)
    (taoLargePrimeSourceUpperCutoff x) H m' ω
  obtain ⟨hIpos, hLone, hUnonneg, hscalar⟩ := hgap
  change 0 < I at hIpos
  change 1 ≤ L at hLone
  change 0 ≤ U at hUnonneg
  change L + L ^ (2 : ℕ) / (8 * I) +
      U * (2000000 + L / (8 * I)) <
      (1 / 2 : ℝ) * B at hscalar
  have hRdiv : L ^ (2 : ℕ) / (8 * I) = R / 8 := by
    dsimp only [R]
    field_simp [hIpos.ne']
  rw [hRdiv] at hscalar
  by_contra hnot
  have hnotData := hnot
  simp only [TaoSourceAntiSieveLargeEvent, not_or, not_lt,
    TaoExceptionalPrimeLargeEvent] at hnotData
  have hE : E ≤ (H : ℝ) * L := by
    simpa only [E, L] using hnotData.1
  have hSraw : S ≤ (H : ℝ) * L ^ (2 : ℕ) / (8 * I) := by
    simpa only [S, L, I] using hnotData.2.1
  have hS : S ≤ (H : ℝ) * (R / 8) := by
    calc
      S ≤ (H : ℝ) * L ^ (2 : ℕ) / (8 * I) := hSraw
      _ = (H : ℝ) * (R / 8) := by
        dsimp only [R]
        field_simp [hIpos.ne']
  have hXraw : X ≤ 2000000 * (H : ℝ) +
      (H : ℝ) * L / (8 * I) := by
    simpa only [X, L, I] using hnotData.2.2
  have hX : X ≤ (H : ℝ) * (2000000 + L / (8 * I)) := by
    calc
      X ≤ 2000000 * (H : ℝ) + (H : ℝ) * L / (8 * I) := hXraw
      _ = (H : ℝ) * (2000000 + L / (8 * I)) := by ring
  have hdet := htypical.three_contributions_lower hx
  change ((H - 1 : ℕ) : ℝ) * B ≤ E + S + U * X at hdet
  have hupper : E + S + U * X ≤
      (H : ℝ) * (L + R / 8 + U * (2000000 + L / (8 * I))) := by
    calc
      E + S + U * X ≤
          (H : ℝ) * L + (H : ℝ) * (R / 8) +
            U * ((H : ℝ) * (2000000 + L / (8 * I))) := by
        gcongr
      _ = (H : ℝ) *
          (L + R / 8 + U * (2000000 + L / (8 * I))) := by ring
  have hscalarNonneg :
      0 ≤ L + R / 8 + U * (2000000 + L / (8 * I)) := by
    have hLpos : 0 < L := zero_lt_one.trans_le hLone
    have hRnonneg : 0 ≤ R := by dsimp only [R]; positivity
    positivity
  have hBpos : 0 < B := by nlinarith
  have hHsubCast : ((H - 1 : ℕ) : ℝ) = (H : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ H)]
    norm_num
  have hhalfH : (H : ℝ) / 2 ≤ ((H - 1 : ℕ) : ℝ) := by
    rw [hHsubCast]
    have hHreal : (2 : ℝ) ≤ H := by exact_mod_cast hHtwo
    linarith
  have hstrict : E + S + U * X < (H : ℝ) * ((1 / 2 : ℝ) * B) :=
    hupper.trans_lt (mul_lt_mul_of_pos_left hscalar hHrealPos)
  have hhalfLower : (H : ℝ) * ((1 / 2 : ℝ) * B) ≤
      ((H - 1 : ℕ) : ℝ) * B := by
    nlinarith
  linarith

/-- Proposition 6.6 before absorbing the much smaller fiftieth-moment tail:
the literal typical event is bounded by the sum of the small- and large-prime
source tails. -/
theorem exists_eventually_measureReal_taoPrimeTupleTypicalEvent_le_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty)
    (H lowerPrime m' : ℕ → ℕ)
    (hH : ∀ᶠ x : ℕ in atTop, H x ≤ taoTypicalLengthCutoff x)
    (hHpos : ∀ᶠ x : ℕ in atTop, 1 ≤ H x) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ x : ℕ in atTop,
      (taoPrimeTupleMeasure (P x) (hP x)).real
          {ω | TaoPrimeTupleTypicalEvent x (H x) (lowerPrime x)
            (taoLargePrimeSourceUpperCutoff x) (m' x) ω} ≤
        A * (8 * iteratedLog x) ^ (50 : ℕ) /
            Real.log (taoZ x) ^ (50 : ℕ) +
          2000001 * (8 * iteratedLog x) ^ (2 : ℕ) /
            ((H x : ℝ) * Real.log (taoZ x) ^ (2 : ℕ)) := by
  obtain ⟨A, hA, htail⟩ :=
    exists_eventually_measureReal_taoSourceAntiSieveLargeEvent_le_of_explicitBurgess
      hC hburgess hscale hP H m' hH hHpos
  refine ⟨A, hA, ?_⟩
  filter_upwards [htail,
    eventually_taoPrimeTupleTypicalEvent_imp_taoSourceAntiSieveLargeEvent] with
      x htailX hinclusion
  exact (measureReal_mono (fun ω hω =>
    hinclusion (H x) (lowerPrime x) (m' x) ω hω)).trans htailX

/-- The same bound on the literal `ENNReal` probability declaration, at the
fixed lower anatomy cutoff used by the source. -/
theorem exists_eventually_taoPrimeTupleTypicalProbability_toReal_le_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty)
    (H m' : ℕ → ℕ)
    (hH : ∀ᶠ x : ℕ in atTop, H x ≤ taoTypicalLengthCutoff x)
    (hHpos : ∀ᶠ x : ℕ in atTop, 1 ≤ H x) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ x : ℕ in atTop,
      (taoPrimeTupleTypicalProbability (P x) (hP x) x (H x)
          (taoZPowerFloor (9 / 10 : ℝ) x)
          (taoLargePrimeSourceUpperCutoff x) (m' x)).toReal ≤
        A * (8 * iteratedLog x) ^ (50 : ℕ) /
            Real.log (taoZ x) ^ (50 : ℕ) +
          2000001 * (8 * iteratedLog x) ^ (2 : ℕ) /
            ((H x : ℝ) * Real.log (taoZ x) ^ (2 : ℕ)) := by
  simpa only [taoPrimeTupleTypicalProbability, Measure.real]
    using exists_eventually_measureReal_taoPrimeTupleTypicalEvent_le_of_explicitBurgess
      hC hburgess hscale hP H
        (fun x => taoZPowerFloor (9 / 10 : ℝ) x) m' hH hHpos

/-- The source length cutoff is eventually at most the forty-eighth power of
`log z`.  This deliberately generous exponent is exactly what is needed to
absorb the fiftieth-moment tail into the final Proposition 6.6 bound. -/
theorem eventually_taoTypicalLengthCutoff_cast_le_log_taoZ_pow_fortyEight :
    ∀ᶠ x : ℕ in atTop,
      (taoTypicalLengthCutoff x : ℝ) ≤
        Real.log (taoZ x) ^ (48 : ℕ) := by
  filter_upwards [
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1 : ℝ)),
    tendsto_iteratedLog_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    (Real.tendsto_log_atTop.comp tendsto_taoZ_atTop).eventually
      (eventually_ge_atTop (8 : ℝ))] with x hlogX hiterX hlogZ
  let L : ℝ := Real.log (taoZ x)
  let I : ℝ := iteratedLog x
  have hL : 8 ≤ L := by simpa only [L] using hlogZ
  have hLpos : 0 < L := by linarith
  have hI : 1 ≤ I := by simpa only [I] using hiterX
  have hIpos : 0 < I := zero_lt_one.trans_le hI
  have hlogXpos : 0 < Real.log x := zero_lt_one.trans_le hlogX
  have hlogXeq : Real.log x = 2 * (L ^ (2 : ℕ) / I) := by
    simpa only [L, I, mul_div_assoc] using
      log_nat_eq_two_mul_log_taoZ_sq_div_iteratedLog hlogXpos hIpos
  have hRle : L ^ (2 : ℕ) / I ≤ L ^ (2 : ℕ) := by
    rw [div_le_iff₀ hIpos]
    nlinarith [sq_nonneg L]
  have hlogXle : Real.log x ≤ 2 * L ^ (2 : ℕ) := by
    rw [hlogXeq]
    gcongr
  have hceil : (taoTypicalLengthCutoff x : ℝ) <
      Real.log x ^ (20 : ℕ) + 1 := by
    simpa only [taoTypicalLengthCutoff] using
      Nat.ceil_lt_add_one (pow_nonneg hlogXpos.le 20)
  have hpowOne : (1 : ℝ) ≤ Real.log x ^ (20 : ℕ) :=
    one_le_pow₀ hlogX
  have hcutoff : (taoTypicalLengthCutoff x : ℝ) ≤
      2 * Real.log x ^ (20 : ℕ) := by linarith
  have hpowLog : Real.log x ^ (20 : ℕ) ≤
      (2 * L ^ (2 : ℕ)) ^ (20 : ℕ) :=
    pow_le_pow_left₀ hlogXpos.le hlogXle 20
  have hconst : (2 : ℝ) ^ (21 : ℕ) ≤ L ^ (8 : ℕ) := by
    calc
      (2 : ℝ) ^ (21 : ℕ) ≤ (8 : ℝ) ^ (8 : ℕ) := by norm_num
      _ ≤ L ^ (8 : ℕ) := pow_le_pow_left₀ (by norm_num) hL 8
  calc
    (taoTypicalLengthCutoff x : ℝ) ≤
        2 * Real.log x ^ (20 : ℕ) := hcutoff
    _ ≤ 2 * (2 * L ^ (2 : ℕ)) ^ (20 : ℕ) := by gcongr
    _ = (2 : ℝ) ^ (21 : ℕ) * L ^ (40 : ℕ) := by ring
    _ ≤ L ^ (8 : ℕ) * L ^ (40 : ℕ) := by
      gcongr
    _ = L ^ (48 : ℕ) := by ring

/-- Source-facing Proposition 6.6: after absorbing the high-moment tail, the
literal typical-tuple probability has the single explicit form
`O((8 log₂ x)^50 / (H log(z)^2))`, which is
`O(1 / (H log^(2-o(1)) z))`. -/
theorem exists_eventually_taoPrimeTupleTypicalProbability_toReal_le_source_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty)
    (H m' : ℕ → ℕ)
    (hH : ∀ᶠ x : ℕ in atTop, H x ≤ taoTypicalLengthCutoff x)
    (hHpos : ∀ᶠ x : ℕ in atTop, 1 ≤ H x) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ x : ℕ in atTop,
      (taoPrimeTupleTypicalProbability (P x) (hP x) x (H x)
          (taoZPowerFloor (9 / 10 : ℝ) x)
          (taoLargePrimeSourceUpperCutoff x) (m' x)).toReal ≤
        B * (8 * iteratedLog x) ^ (50 : ℕ) /
          ((H x : ℝ) * Real.log (taoZ x) ^ (2 : ℕ)) := by
  obtain ⟨A, hA, hprob⟩ :=
    exists_eventually_taoPrimeTupleTypicalProbability_toReal_le_of_explicitBurgess
      hC hburgess hscale hP H m' hH hHpos
  let B : ℝ := A + 2000001
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨B, hB, ?_⟩
  filter_upwards [hprob, hH,
    eventually_taoTypicalLengthCutoff_cast_le_log_taoZ_pow_fortyEight,
    hHpos,
    tendsto_iteratedLog_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    (Real.tendsto_log_atTop.comp tendsto_taoZ_atTop).eventually
      (eventually_gt_atTop (0 : ℝ))] with
      x hprobX hHx hcutoff hHxPos hiterX hlogZ
  let L : ℝ := Real.log (taoZ x)
  let J : ℝ := 8 * iteratedLog x
  let D : ℝ := (H x : ℝ) * L ^ (2 : ℕ)
  have hLpos : 0 < L := by simpa only [L] using hlogZ
  have hHrealPos : (0 : ℝ) < H x := by exact_mod_cast hHxPos
  have hJone : 1 ≤ J := by dsimp only [J]; nlinarith
  have hDpos : 0 < D := by dsimp only [D]; positivity
  have hHcast : (H x : ℝ) ≤ L ^ (48 : ℕ) := by
    have hHxReal : (H x : ℝ) ≤ taoTypicalLengthCutoff x := by
      exact_mod_cast hHx
    exact hHxReal.trans (by simpa only [L] using hcutoff)
  have hdenom : D ≤ L ^ (50 : ℕ) := by
    dsimp only [D]
    calc
      (H x : ℝ) * L ^ (2 : ℕ) ≤
          L ^ (48 : ℕ) * L ^ (2 : ℕ) := by gcongr
      _ = L ^ (50 : ℕ) := by ring
  have hfirst : A * J ^ (50 : ℕ) / L ^ (50 : ℕ) ≤
      A * J ^ (50 : ℕ) / D :=
    div_le_div_of_nonneg_left (by positivity) hDpos hdenom
  have hJpow : J ^ (2 : ℕ) ≤ J ^ (50 : ℕ) :=
    pow_le_pow_right₀ hJone (by norm_num : (2 : ℕ) ≤ 50)
  have hsecond : 2000001 * J ^ (2 : ℕ) / D ≤
      2000001 * J ^ (50 : ℕ) / D := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hJpow (by norm_num)) hDpos.le
  calc
    (taoPrimeTupleTypicalProbability (P x) (hP x) x (H x)
        (taoZPowerFloor (9 / 10 : ℝ) x)
        (taoLargePrimeSourceUpperCutoff x) (m' x)).toReal ≤
      A * J ^ (50 : ℕ) / L ^ (50 : ℕ) +
        2000001 * J ^ (2 : ℕ) / D := by
      simpa only [J, L, D] using hprobX
    _ ≤ A * J ^ (50 : ℕ) / D +
        2000001 * J ^ (50 : ℕ) / D := add_le_add hfirst hsecond
    _ = B * J ^ (50 : ℕ) / D := by
      dsimp only [B]
      ring

end

end Tao2026
