import Tao2026.BadIntervalRandomModel

/-!
# The large-prime mean and variance expansion for Proposition 6.6

This module formalizes the exact finite probability algebra behind the source's
large-prime branch.  The contribution is the unweighted sum over shifts
`1 ≤ l < H` and primes in a prescribed interval.  Its mean is a sum of
single divisibility probabilities and its variance is a double sum of
covariances.  On the source range `H ≤ lowerPrime`, distinct shifts carrying
the same prime have empty joint event and hence nonpositive covariance.

The analytic first- and second-moment estimates of Propositions 6.7 and 6.8
are deliberately not asserted here.
-/

namespace Tao2026

open MeasureTheory ProbabilityTheory
open scoped Classical

noncomputable section

def taoLargeAntiSievePrimeRange (lowerPrime upperPrime : ℕ) : Finset ℕ :=
  (Finset.Ioc lowerPrime upperPrime).filter Nat.Prime

def taoLargeAntiSieveIndices (lowerPrime upperPrime H : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ico 1 H).product (taoLargeAntiSievePrimeRange lowerPrime upperPrime)

def TaoLargePrimeDivisibilityEvent (m' : ℕ) (lp : ℕ × ℕ) (w : TaoPrimeTuple) : Prop :=
  lp.2 ∣ taoPrimeTupleStart m' w + lp.1

def taoLargePrimeContribution (lowerPrime upperPrime H m' : ℕ) (w : TaoPrimeTuple) : ℝ :=
  ∑ lp ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H,
    taoPrimeDivisibilityIndicator m' lp.1 lp.2 w

def taoLargePrimeMean
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (lowerPrime upperPrime H m' : ℕ) : ℝ :=
  ∫ w, taoLargePrimeContribution lowerPrime upperPrime H m' w ∂taoPrimeTupleMeasure P hP

theorem taoLargePrimeDivisibilityIndicator_eq (m' : ℕ) (lp : ℕ × ℕ) :
    (fun w : TaoPrimeTuple => taoPrimeDivisibilityIndicator m' lp.1 lp.2 w) =
      {w : TaoPrimeTuple | TaoLargePrimeDivisibilityEvent m' lp w}.indicator (fun _ => (1 : ℝ)) := by
  funext w
  by_cases h : TaoLargePrimeDivisibilityEvent m' lp w <;>
    simp [TaoLargePrimeDivisibilityEvent, taoPrimeDivisibilityIndicator, Set.indicator]

theorem integrable_taoLargePrimeDivisibilityIndicator
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (m' : ℕ) (lp : ℕ × ℕ) :
    Integrable (fun w : TaoPrimeTuple =>
      taoPrimeDivisibilityIndicator m' lp.1 lp.2 w)
      (taoPrimeTupleMeasure P hP) := by
  have hm : MeasurableSet {w : TaoPrimeTuple | TaoLargePrimeDivisibilityEvent m' lp w} :=
    (Set.to_countable _).measurableSet
  have hi : Integrable
      ({w : TaoPrimeTuple | TaoLargePrimeDivisibilityEvent m' lp w}.indicator (fun _ => (1 : ℝ)))
      (taoPrimeTupleMeasure P hP) := (integrable_const (1 : ℝ)).indicator hm
  rw [taoLargePrimeDivisibilityIndicator_eq]
  exact hi

theorem taoLargePrimeMean_eq
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (lowerPrime upperPrime H m' : ℕ) :
    taoLargePrimeMean P hP lowerPrime upperPrime H m' =
      ∑ lp ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H,
        (taoPrimeTupleMeasure P hP).real {w | TaoLargePrimeDivisibilityEvent m' lp w} := by
  unfold taoLargePrimeMean taoLargePrimeContribution
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro lp hlp
    have hm : MeasurableSet {w : TaoPrimeTuple | TaoLargePrimeDivisibilityEvent m' lp w} :=
      (Set.to_countable _).measurableSet
    rw [taoLargePrimeDivisibilityIndicator_eq]
    exact integral_indicator_one hm
  · intro lp hlp
    exact integrable_taoLargePrimeDivisibilityIndicator P hP m' lp

def TaoLargePrimeJointDivisibilityEvent (m' : ℕ) (a b : ℕ × ℕ) (w : TaoPrimeTuple) : Prop :=
  TaoLargePrimeDivisibilityEvent m' a w ∧ TaoLargePrimeDivisibilityEvent m' b w

theorem taoLargePrimeIndicator_mul_eq (m' : ℕ) (a b : ℕ × ℕ) :
    (fun w : TaoPrimeTuple =>
      taoPrimeDivisibilityIndicator m' a.1 a.2 w *
        taoPrimeDivisibilityIndicator m' b.1 b.2 w) =
      {w : TaoPrimeTuple | TaoLargePrimeJointDivisibilityEvent m' a b w}.indicator
        (fun _ => (1 : ℝ)) := by
  funext w
  by_cases ha : TaoLargePrimeDivisibilityEvent m' a w <;>
    by_cases hb : TaoLargePrimeDivisibilityEvent m' b w
  all_goals simp only [TaoLargePrimeDivisibilityEvent] at ha hb
  all_goals simp [TaoLargePrimeJointDivisibilityEvent, TaoLargePrimeDivisibilityEvent, taoPrimeDivisibilityIndicator,
    Set.indicator, ha, hb]

theorem integrable_taoLargePrimeIndicator_mul
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (m' : ℕ) (a b : ℕ × ℕ) :
    Integrable (fun w : TaoPrimeTuple =>
      taoPrimeDivisibilityIndicator m' a.1 a.2 w *
        taoPrimeDivisibilityIndicator m' b.1 b.2 w)
      (taoPrimeTupleMeasure P hP) := by
  have hm : MeasurableSet {w : TaoPrimeTuple | TaoLargePrimeJointDivisibilityEvent m' a b w} :=
    (Set.to_countable _).measurableSet
  rw [taoLargePrimeIndicator_mul_eq]
  exact (integrable_const (1 : ℝ)).indicator hm

def taoLargePrimeSecondMoment
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (lowerPrime upperPrime H m' : ℕ) : ℝ :=
  ∫ w, (taoLargePrimeContribution lowerPrime upperPrime H m' w) ^ (2 : ℕ)
    ∂taoPrimeTupleMeasure P hP

theorem taoLargePrimeContribution_sq (lowerPrime upperPrime H m' : ℕ)
    (w : TaoPrimeTuple) :
    (taoLargePrimeContribution lowerPrime upperPrime H m' w) ^ (2 : ℕ) =
      ∑ a ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H,
        ∑ b ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H,
          taoPrimeDivisibilityIndicator m' a.1 a.2 w *
            taoPrimeDivisibilityIndicator m' b.1 b.2 w := by
  unfold taoLargePrimeContribution
  rw [pow_two, Finset.sum_mul_sum]

theorem taoLargePrimeSecondMoment_eq
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (lowerPrime upperPrime H m' : ℕ) :
    taoLargePrimeSecondMoment P hP lowerPrime upperPrime H m' =
      ∑ a ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H,
        ∑ b ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H,
          (taoPrimeTupleMeasure P hP).real {w | TaoLargePrimeJointDivisibilityEvent m' a b w} := by
  let S := taoLargeAntiSieveIndices lowerPrime upperPrime H
  unfold taoLargePrimeSecondMoment
  calc
    (∫ w, (taoLargePrimeContribution lowerPrime upperPrime H m' w) ^ (2 : ℕ)
        ∂taoPrimeTupleMeasure P hP) =
      ∫ w, ∑ a ∈ S, ∑ b ∈ S,
        taoPrimeDivisibilityIndicator m' a.1 a.2 w *
          taoPrimeDivisibilityIndicator m' b.1 b.2 w
        ∂taoPrimeTupleMeasure P hP := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun w =>
        taoLargePrimeContribution_sq lowerPrime upperPrime H m' w
    _ = ∑ a ∈ S, ∫ w, ∑ b ∈ S,
        taoPrimeDivisibilityIndicator m' a.1 a.2 w *
          taoPrimeDivisibilityIndicator m' b.1 b.2 w
        ∂taoPrimeTupleMeasure P hP := by
      exact integral_finsetSum S fun a ha => integrable_finsetSum S fun b hb =>
        integrable_taoLargePrimeIndicator_mul P hP m' a b
    _ = ∑ a ∈ S, ∑ b ∈ S, ∫ w,
        taoPrimeDivisibilityIndicator m' a.1 a.2 w *
          taoPrimeDivisibilityIndicator m' b.1 b.2 w
        ∂taoPrimeTupleMeasure P hP := by
      apply Finset.sum_congr rfl
      intro a ha
      exact integral_finsetSum S fun b hb =>
        integrable_taoLargePrimeIndicator_mul P hP m' a b
    _ = ∑ a ∈ S, ∑ b ∈ S,
        (taoPrimeTupleMeasure P hP).real {w | TaoLargePrimeJointDivisibilityEvent m' a b w} := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      have hm : MeasurableSet {w : TaoPrimeTuple | TaoLargePrimeJointDivisibilityEvent m' a b w} :=
        (Set.to_countable _).measurableSet
      rw [taoLargePrimeIndicator_mul_eq]
      exact integral_indicator_one hm

def taoLargePrimeProbability
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (m' : ℕ) (a : ℕ × ℕ) : ℝ :=
  (taoPrimeTupleMeasure P hP).real {w | TaoLargePrimeDivisibilityEvent m' a w}

def taoLargePrimeJointProbability
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (m' : ℕ) (a b : ℕ × ℕ) : ℝ :=
  (taoPrimeTupleMeasure P hP).real {w | TaoLargePrimeJointDivisibilityEvent m' a b w}

def taoLargePrimeCovariance
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (m' : ℕ) (a b : ℕ × ℕ) : ℝ :=
  taoLargePrimeJointProbability P hP m' a b -
    taoLargePrimeProbability P hP m' a * taoLargePrimeProbability P hP m' b

def taoLargePrimeVariance
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (lowerPrime upperPrime H m' : ℕ) : ℝ :=
  taoLargePrimeSecondMoment P hP lowerPrime upperPrime H m' -
    taoLargePrimeMean P hP lowerPrime upperPrime H m' ^ (2 : ℕ)

theorem taoLargePrimeVariance_eq
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (lowerPrime upperPrime H m' : ℕ) :
    taoLargePrimeVariance P hP lowerPrime upperPrime H m' =
      ∑ a ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H,
        ∑ b ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H,
          taoLargePrimeCovariance P hP m' a b := by
  rw [taoLargePrimeVariance, taoLargePrimeSecondMoment_eq, taoLargePrimeMean_eq, pow_two, Finset.sum_mul_sum]
  simp only [taoLargePrimeCovariance, taoLargePrimeJointProbability, taoLargePrimeProbability,
    Finset.sum_sub_distrib]

theorem mem_taoLargeAntiSievePrimeRange {lowerPrime upperPrime p : ℕ} :
    p ∈ taoLargeAntiSievePrimeRange lowerPrime upperPrime ↔
      Nat.Prime p ∧ lowerPrime < p ∧ p ≤ upperPrime := by
  simp [taoLargeAntiSievePrimeRange, and_assoc, and_comm]

theorem mem_taoLargeAntiSieveIndices {lowerPrime upperPrime H l p : ℕ} :
    (l, p) ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H ↔
      1 ≤ l ∧ l < H ∧ Nat.Prime p ∧
        lowerPrime < p ∧ p ≤ upperPrime := by
  simp [taoLargeAntiSieveIndices, mem_taoLargeAntiSievePrimeRange, and_assoc,
    and_left_comm, and_comm]

theorem taoLargePrimeProbability_nonneg
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (m' : ℕ) (a : ℕ × ℕ) :
    0 ≤ taoLargePrimeProbability P hP m' a := by
  exact MeasureTheory.measureReal_nonneg

/-- A modulus dividing the fixed factor `m'` cannot divide a nonzero shift:
the random tuple start already contains `m'` as a factor. -/
theorem not_taoLargePrimeDivisibilityEvent_of_dvd_base
    {m' : ℕ} {a : ℕ × ℕ} (hm : a.2 ∣ m') (ha : ¬a.2 ∣ a.1)
    (w : TaoPrimeTuple) : ¬TaoLargePrimeDivisibilityEvent m' a w := by
  intro hw
  have hstart : a.2 ∣ taoPrimeTupleStart m' w := by
    unfold taoPrimeTupleStart
    exact dvd_mul_of_dvd_right hm _
  exact ha ((Nat.dvd_add_iff_right hstart).mpr hw)

theorem taoLargePrimeProbability_eq_zero_of_dvd_base
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    {m' : ℕ} {a : ℕ × ℕ} (hm : a.2 ∣ m') (ha : ¬a.2 ∣ a.1) :
    taoLargePrimeProbability P hP m' a = 0 := by
  rw [taoLargePrimeProbability, show
    {w : TaoPrimeTuple | TaoLargePrimeDivisibilityEvent m' a w} = ∅ by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact not_taoLargePrimeDivisibilityEvent_of_dvd_base hm ha w]
  exact MeasureTheory.measureReal_empty

theorem taoLargePrimeJointProbability_eq_zero_of_left_dvd_base
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    {m' : ℕ} {a b : ℕ × ℕ} (hm : a.2 ∣ m') (ha : ¬a.2 ∣ a.1) :
    taoLargePrimeJointProbability P hP m' a b = 0 := by
  rw [taoLargePrimeJointProbability, show
    {w : TaoPrimeTuple | TaoLargePrimeJointDivisibilityEvent m' a b w} = ∅ by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hw
      exact not_taoLargePrimeDivisibilityEvent_of_dvd_base hm ha w hw.1]
  exact MeasureTheory.measureReal_empty

theorem taoLargePrimeJointProbability_eq_zero_of_right_dvd_base
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    {m' : ℕ} {a b : ℕ × ℕ} (hm : b.2 ∣ m') (hb : ¬b.2 ∣ b.1) :
    taoLargePrimeJointProbability P hP m' a b = 0 := by
  rw [taoLargePrimeJointProbability, show
    {w : TaoPrimeTuple | TaoLargePrimeJointDivisibilityEvent m' a b w} = ∅ by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hw
      exact not_taoLargePrimeDivisibilityEvent_of_dvd_base hm hb w hw.2]
  exact MeasureTheory.measureReal_empty

theorem taoLargePrimeCovariance_eq_zero_of_left_dvd_base
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    {m' : ℕ} {a b : ℕ × ℕ} (hm : a.2 ∣ m') (ha : ¬a.2 ∣ a.1) :
    taoLargePrimeCovariance P hP m' a b = 0 := by
  rw [taoLargePrimeCovariance,
    taoLargePrimeJointProbability_eq_zero_of_left_dvd_base P hP hm ha,
    taoLargePrimeProbability_eq_zero_of_dvd_base P hP hm ha]
  ring

theorem taoLargePrimeCovariance_eq_zero_of_right_dvd_base
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    {m' : ℕ} {a b : ℕ × ℕ} (hm : b.2 ∣ m') (hb : ¬b.2 ∣ b.1) :
    taoLargePrimeCovariance P hP m' a b = 0 := by
  rw [taoLargePrimeCovariance,
    taoLargePrimeJointProbability_eq_zero_of_right_dvd_base P hP hm hb,
    taoLargePrimeProbability_eq_zero_of_dvd_base P hP hm hb]
  ring

theorem taoLargePrimeJointProbability_self
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (m' : ℕ) (a : ℕ × ℕ) :
    taoLargePrimeJointProbability P hP m' a a = taoLargePrimeProbability P hP m' a := by
  unfold taoLargePrimeJointProbability taoLargePrimeProbability
  rw [show {w : TaoPrimeTuple | TaoLargePrimeJointDivisibilityEvent m' a a w} =
      {w : TaoPrimeTuple | TaoLargePrimeDivisibilityEvent m' a w} by
    ext w
    simp [TaoLargePrimeJointDivisibilityEvent]]

theorem taoLargePrimeCovariance_self_le_probability
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (m' : ℕ) (a : ℕ × ℕ) :
    taoLargePrimeCovariance P hP m' a a ≤ taoLargePrimeProbability P hP m' a := by
  rw [taoLargePrimeCovariance, taoLargePrimeJointProbability_self]
  nlinarith [sq_nonneg (taoLargePrimeProbability P hP m' a)]

theorem taoLargePrimeJointDivisibilityEvent_empty_of_same_prime
    {lowerPrime upperPrime H m' : ℕ} {a b : ℕ × ℕ}
    (haMem : a ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H)
    (hbMem : b ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H)
    (hH : H ≤ lowerPrime) (hp : a.2 = b.2) (hl : a.1 ≠ b.1) :
    {w : TaoPrimeTuple | TaoLargePrimeJointDivisibilityEvent m' a b w} = ∅ := by
  ext w
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨ha, hb⟩
  have hsum : taoPrimeTupleStart m' w + a.1 ≡
      taoPrimeTupleStart m' w + b.1 [MOD a.2] :=
    ha.modEq_zero_nat.trans (by simpa [hp] using hb.modEq_zero_nat.symm)
  have hshifts : a.1 ≡ b.1 [MOD a.2] :=
    Nat.ModEq.add_left_cancel' (taoPrimeTupleStart m' w) hsum
  have haData := mem_taoLargeAntiSieveIndices.mp haMem
  have hbData := mem_taoLargeAntiSieveIndices.mp hbMem
  have haLt : a.1 < a.2 :=
    lt_of_lt_of_le haData.2.1 (le_trans hH (Nat.le_of_lt haData.2.2.2.1))
  have hbLt : b.1 < a.2 := by
    have hbPrimeLt : lowerPrime < a.2 := by
      simpa [hp] using hbData.2.2.2.1
    apply lt_of_lt_of_le hbData.2.1
    exact le_trans hH (Nat.le_of_lt hbPrimeLt)
  exact hl (hshifts.eq_of_lt_of_lt haLt hbLt)

theorem taoLargePrimeJointProbability_eq_zero_of_same_prime
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    {lowerPrime upperPrime H m' : ℕ} {a b : ℕ × ℕ}
    (haMem : a ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H)
    (hbMem : b ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H)
    (hH : H ≤ lowerPrime) (hp : a.2 = b.2) (hl : a.1 ≠ b.1) :
    taoLargePrimeJointProbability P hP m' a b = 0 := by
  rw [taoLargePrimeJointProbability,
    taoLargePrimeJointDivisibilityEvent_empty_of_same_prime haMem hbMem hH hp hl]
  exact MeasureTheory.measureReal_empty

theorem taoLargePrimeCovariance_nonpos_of_same_prime
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    {lowerPrime upperPrime H m' : ℕ} {a b : ℕ × ℕ}
    (haMem : a ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H)
    (hbMem : b ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H)
    (hH : H ≤ lowerPrime) (hp : a.2 = b.2) (hl : a.1 ≠ b.1) :
    taoLargePrimeCovariance P hP m' a b ≤ 0 := by
  rw [taoLargePrimeCovariance,
    taoLargePrimeJointProbability_eq_zero_of_same_prime P hP haMem hbMem hH hp hl]
  simpa only [zero_sub] using neg_nonpos.mpr (mul_nonneg
    (taoLargePrimeProbability_nonneg P hP m' a)
    (taoLargePrimeProbability_nonneg P hP m' b))

/-- In one covariance row, the diagonal costs at most the corresponding
probability, all other same-prime entries are nonpositive, and only pairs
with distinct primes remain. -/
theorem sum_taoLargePrimeCovariance_le_probability_add_distinctPrimes
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    {lowerPrime upperPrime H m' : ℕ} {a : ℕ × ℕ}
    (haMem : a ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H)
    (hH : H ≤ lowerPrime) :
    (∑ b ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H,
      taoLargePrimeCovariance P hP m' a b) ≤
      taoLargePrimeProbability P hP m' a +
        ∑ b ∈ (taoLargeAntiSieveIndices lowerPrime upperPrime H).filter
          (fun b => b.2 ≠ a.2), taoLargePrimeCovariance P hP m' a b := by
  let S := taoLargeAntiSieveIndices lowerPrime upperPrime H
  let same := S.filter fun b => b.2 = a.2
  have haSame : a ∈ same := by simp [same, S, haMem]
  have hsame : (∑ b ∈ same, taoLargePrimeCovariance P hP m' a b) ≤
      taoLargePrimeProbability P hP m' a := by
    rw [Finset.sum_eq_add_sum_diff_singleton_of_mem haSame]
    calc
      taoLargePrimeCovariance P hP m' a a +
          ∑ b ∈ same \ {a}, taoLargePrimeCovariance P hP m' a b ≤
        taoLargePrimeProbability P hP m' a + 0 := by
          apply add_le_add (taoLargePrimeCovariance_self_le_probability P hP m' a)
          apply Finset.sum_nonpos
          intro b hb
          have hbData := Finset.mem_sdiff.mp hb
          have hbSame := hbData.1
          have hbMem : b ∈ S := (Finset.mem_filter.mp hbSame).1
          have hp : a.2 = b.2 := (Finset.mem_filter.mp hbSame).2.symm
          have hab : a ≠ b := by
            intro hab
            exact hbData.2 (by simp [hab])
          have hl : a.1 ≠ b.1 := by
            intro hfirst
            apply hab
            exact Prod.ext hfirst hp
          exact taoLargePrimeCovariance_nonpos_of_same_prime
            P hP (by simpa [S] using haMem) (by simpa [S] using hbMem)
              hH hp hl
      _ = taoLargePrimeProbability P hP m' a := add_zero _
  calc
    (∑ b ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H,
        taoLargePrimeCovariance P hP m' a b) =
      (∑ b ∈ same, taoLargePrimeCovariance P hP m' a b) +
        ∑ b ∈ S.filter (fun b => ¬b.2 = a.2),
          taoLargePrimeCovariance P hP m' a b := by
            rw [← Finset.sum_filter_add_sum_filter_not S
              (fun b => b.2 = a.2)]
    _ ≤ taoLargePrimeProbability P hP m' a +
        ∑ b ∈ S.filter (fun b => ¬b.2 = a.2),
          taoLargePrimeCovariance P hP m' a b :=
            add_le_add hsame (le_refl _)
    _ = taoLargePrimeProbability P hP m' a +
        ∑ b ∈ (taoLargeAntiSieveIndices lowerPrime upperPrime H).filter
          (fun b => b.2 ≠ a.2), taoLargePrimeCovariance P hP m' a b := by
      rfl

/-- Source-facing variance reduction: after the diagonal contribution, only
ordered pairs carrying distinct primes can contribute positively. -/
theorem taoLargePrimeVariance_le_mean_add_distinctPrimeCovariances
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (lowerPrime upperPrime H m' : ℕ) (hH : H ≤ lowerPrime) :
    taoLargePrimeVariance P hP lowerPrime upperPrime H m' ≤
      taoLargePrimeMean P hP lowerPrime upperPrime H m' +
        ∑ a ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H,
          ∑ b ∈ (taoLargeAntiSieveIndices lowerPrime upperPrime H).filter
            (fun b => b.2 ≠ a.2), taoLargePrimeCovariance P hP m' a b := by
  rw [taoLargePrimeVariance_eq, taoLargePrimeMean_eq]
  calc
    (∑ a ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H,
        ∑ b ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H,
          taoLargePrimeCovariance P hP m' a b) ≤
      ∑ a ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H,
        (taoLargePrimeProbability P hP m' a +
          ∑ b ∈ (taoLargeAntiSieveIndices lowerPrime upperPrime H).filter
            (fun b => b.2 ≠ a.2), taoLargePrimeCovariance P hP m' a b) := by
        apply Finset.sum_le_sum
        intro a ha
        exact sum_taoLargePrimeCovariance_le_probability_add_distinctPrimes
          P hP ha hH
    _ = (∑ a ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H,
          taoLargePrimeProbability P hP m' a) +
        ∑ a ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H,
          ∑ b ∈ (taoLargeAntiSieveIndices lowerPrime upperPrime H).filter
            (fun b => b.2 ≠ a.2), taoLargePrimeCovariance P hP m' a b := by
      rw [Finset.sum_add_distrib]

end

end Tao2026
