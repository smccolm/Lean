import Tao2026.BadIntervalBackwardSmallPrime

/-!
# Backward typical intervals: large-prime probability algebra

This is the exact mean/variance layer for divisibility of the right-endpoint
product `v` through the preceding values `v-l`.  The modular event `v ≡ l`
is also identified with the already analyzed forward residue at shift `p-l`
whenever `l<p`; this lets the analytic character estimates be reused without
changing their residue-independent constants.
-/

namespace Tao2026

open MeasureTheory ProbabilityTheory
open scoped Classical

noncomputable section

set_option maxRecDepth 12000
set_option maxHeartbeats 800000

def TaoBackwardLargePrimeDivisibilityEvent
    (m' : ℕ) (lp : ℕ × ℕ) (ω : TaoPrimeTuple) : Prop :=
  taoPrimeTupleStart m' ω ≡ lp.1 [MOD lp.2]

def taoBackwardLargePrimeContribution
    (lowerPrime upperPrime H m' : ℕ) (ω : TaoPrimeTuple) : ℝ :=
  ∑ lp ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H,
    taoBackwardPrimeDivisibilityIndicator m' lp.1 lp.2 ω

def taoBackwardLargePrimeMean
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (lowerPrime upperPrime H m' : ℕ) : ℝ :=
  ∫ ω, taoBackwardLargePrimeContribution lowerPrime upperPrime H m' ω
    ∂taoPrimeTupleMeasure P hP

theorem taoBackwardLargePrimeDivisibilityIndicator_eq
    (m' : ℕ) (lp : ℕ × ℕ) :
    (fun ω : TaoPrimeTuple =>
      taoBackwardPrimeDivisibilityIndicator m' lp.1 lp.2 ω) =
      {ω : TaoPrimeTuple |
        TaoBackwardLargePrimeDivisibilityEvent m' lp ω}.indicator
          (fun _ => (1 : ℝ)) := by
  funext ω
  by_cases h : TaoBackwardLargePrimeDivisibilityEvent m' lp ω <;>
    simp [TaoBackwardLargePrimeDivisibilityEvent,
      taoBackwardPrimeDivisibilityIndicator, Set.indicator]

theorem integrable_taoBackwardLargePrimeDivisibilityIndicator
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (m' : ℕ) (lp : ℕ × ℕ) :
    Integrable (fun ω : TaoPrimeTuple =>
      taoBackwardPrimeDivisibilityIndicator m' lp.1 lp.2 ω)
      (taoPrimeTupleMeasure P hP) := by
  have hm : MeasurableSet {ω : TaoPrimeTuple |
      TaoBackwardLargePrimeDivisibilityEvent m' lp ω} :=
    (Set.to_countable _).measurableSet
  have hi : Integrable
      ({ω : TaoPrimeTuple |
        TaoBackwardLargePrimeDivisibilityEvent m' lp ω}.indicator
          (fun _ => (1 : ℝ))) (taoPrimeTupleMeasure P hP) :=
    (integrable_const (1 : ℝ)).indicator hm
  rw [taoBackwardLargePrimeDivisibilityIndicator_eq]
  exact hi

theorem taoBackwardLargePrimeMean_eq
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (lowerPrime upperPrime H m' : ℕ) :
    taoBackwardLargePrimeMean P hP lowerPrime upperPrime H m' =
      ∑ lp ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H,
        (taoPrimeTupleMeasure P hP).real
          {ω | TaoBackwardLargePrimeDivisibilityEvent m' lp ω} := by
  unfold taoBackwardLargePrimeMean taoBackwardLargePrimeContribution
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro lp _hlp
    have hm : MeasurableSet {ω : TaoPrimeTuple |
        TaoBackwardLargePrimeDivisibilityEvent m' lp ω} :=
      (Set.to_countable _).measurableSet
    rw [taoBackwardLargePrimeDivisibilityIndicator_eq]
    exact integral_indicator_one hm
  · intro lp _hlp
    exact integrable_taoBackwardLargePrimeDivisibilityIndicator P hP m' lp

def TaoBackwardLargePrimeJointDivisibilityEvent
    (m' : ℕ) (a b : ℕ × ℕ) (ω : TaoPrimeTuple) : Prop :=
  TaoBackwardLargePrimeDivisibilityEvent m' a ω ∧
    TaoBackwardLargePrimeDivisibilityEvent m' b ω

theorem taoBackwardLargePrimeIndicator_mul_eq
    (m' : ℕ) (a b : ℕ × ℕ) :
    (fun ω : TaoPrimeTuple =>
      taoBackwardPrimeDivisibilityIndicator m' a.1 a.2 ω *
        taoBackwardPrimeDivisibilityIndicator m' b.1 b.2 ω) =
      {ω : TaoPrimeTuple |
        TaoBackwardLargePrimeJointDivisibilityEvent m' a b ω}.indicator
          (fun _ => (1 : ℝ)) := by
  funext ω
  by_cases ha : TaoBackwardLargePrimeDivisibilityEvent m' a ω <;>
    by_cases hb : TaoBackwardLargePrimeDivisibilityEvent m' b ω
  all_goals simp only [TaoBackwardLargePrimeDivisibilityEvent] at ha hb
  all_goals simp [TaoBackwardLargePrimeJointDivisibilityEvent,
    TaoBackwardLargePrimeDivisibilityEvent,
    taoBackwardPrimeDivisibilityIndicator, Set.indicator, ha, hb]

theorem integrable_taoBackwardLargePrimeIndicator_mul
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (m' : ℕ) (a b : ℕ × ℕ) :
    Integrable (fun ω : TaoPrimeTuple =>
      taoBackwardPrimeDivisibilityIndicator m' a.1 a.2 ω *
        taoBackwardPrimeDivisibilityIndicator m' b.1 b.2 ω)
      (taoPrimeTupleMeasure P hP) := by
  have hm : MeasurableSet {ω : TaoPrimeTuple |
      TaoBackwardLargePrimeJointDivisibilityEvent m' a b ω} :=
    (Set.to_countable _).measurableSet
  rw [taoBackwardLargePrimeIndicator_mul_eq]
  exact (integrable_const (1 : ℝ)).indicator hm

def taoBackwardLargePrimeSecondMoment
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (lowerPrime upperPrime H m' : ℕ) : ℝ :=
  ∫ ω, (taoBackwardLargePrimeContribution
      lowerPrime upperPrime H m' ω) ^ (2 : ℕ)
    ∂taoPrimeTupleMeasure P hP

theorem taoBackwardLargePrimeContribution_sq
    (lowerPrime upperPrime H m' : ℕ) (ω : TaoPrimeTuple) :
    (taoBackwardLargePrimeContribution lowerPrime upperPrime H m' ω) ^
        (2 : ℕ) =
      ∑ a ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H,
        ∑ b ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H,
          taoBackwardPrimeDivisibilityIndicator m' a.1 a.2 ω *
            taoBackwardPrimeDivisibilityIndicator m' b.1 b.2 ω := by
  unfold taoBackwardLargePrimeContribution
  rw [pow_two, Finset.sum_mul_sum]

theorem taoBackwardLargePrimeSecondMoment_eq
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (lowerPrime upperPrime H m' : ℕ) :
    taoBackwardLargePrimeSecondMoment P hP lowerPrime upperPrime H m' =
      ∑ a ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H,
        ∑ b ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H,
          (taoPrimeTupleMeasure P hP).real
            {ω | TaoBackwardLargePrimeJointDivisibilityEvent m' a b ω} := by
  let S := taoLargeAntiSieveIndices lowerPrime upperPrime H
  unfold taoBackwardLargePrimeSecondMoment
  calc
    (∫ ω, (taoBackwardLargePrimeContribution
        lowerPrime upperPrime H m' ω) ^ (2 : ℕ)
        ∂taoPrimeTupleMeasure P hP) =
      ∫ ω, ∑ a ∈ S, ∑ b ∈ S,
        taoBackwardPrimeDivisibilityIndicator m' a.1 a.2 ω *
          taoBackwardPrimeDivisibilityIndicator m' b.1 b.2 ω
        ∂taoPrimeTupleMeasure P hP := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω =>
        taoBackwardLargePrimeContribution_sq lowerPrime upperPrime H m' ω
    _ = ∑ a ∈ S, ∫ ω, ∑ b ∈ S,
        taoBackwardPrimeDivisibilityIndicator m' a.1 a.2 ω *
          taoBackwardPrimeDivisibilityIndicator m' b.1 b.2 ω
        ∂taoPrimeTupleMeasure P hP := by
      exact integral_finsetSum S fun a _ha =>
        integrable_finsetSum S fun b _hb =>
          integrable_taoBackwardLargePrimeIndicator_mul P hP m' a b
    _ = ∑ a ∈ S, ∑ b ∈ S, ∫ ω,
        taoBackwardPrimeDivisibilityIndicator m' a.1 a.2 ω *
          taoBackwardPrimeDivisibilityIndicator m' b.1 b.2 ω
        ∂taoPrimeTupleMeasure P hP := by
      apply Finset.sum_congr rfl
      intro a _ha
      exact integral_finsetSum S fun b _hb =>
        integrable_taoBackwardLargePrimeIndicator_mul P hP m' a b
    _ = ∑ a ∈ S, ∑ b ∈ S,
        (taoPrimeTupleMeasure P hP).real
          {ω | TaoBackwardLargePrimeJointDivisibilityEvent m' a b ω} := by
      apply Finset.sum_congr rfl
      intro a _ha
      apply Finset.sum_congr rfl
      intro b _hb
      have hm : MeasurableSet {ω : TaoPrimeTuple |
          TaoBackwardLargePrimeJointDivisibilityEvent m' a b ω} :=
        (Set.to_countable _).measurableSet
      rw [taoBackwardLargePrimeIndicator_mul_eq]
      exact integral_indicator_one hm

def taoBackwardLargePrimeProbability
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (m' : ℕ) (a : ℕ × ℕ) : ℝ :=
  (taoPrimeTupleMeasure P hP).real
    {ω | TaoBackwardLargePrimeDivisibilityEvent m' a ω}

def taoBackwardLargePrimeJointProbability
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (m' : ℕ) (a b : ℕ × ℕ) : ℝ :=
  (taoPrimeTupleMeasure P hP).real
    {ω | TaoBackwardLargePrimeJointDivisibilityEvent m' a b ω}

def taoBackwardLargePrimeCovariance
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (m' : ℕ) (a b : ℕ × ℕ) : ℝ :=
  taoBackwardLargePrimeJointProbability P hP m' a b -
    taoBackwardLargePrimeProbability P hP m' a *
      taoBackwardLargePrimeProbability P hP m' b

theorem taoBackwardLargePrimeJointProbability_comm
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (m' : ℕ) (a b : ℕ × ℕ) :
    taoBackwardLargePrimeJointProbability P hP m' a b =
      taoBackwardLargePrimeJointProbability P hP m' b a := by
  unfold taoBackwardLargePrimeJointProbability
  congr 2
  ext ω
  simp only [TaoBackwardLargePrimeJointDivisibilityEvent]
  tauto

theorem taoBackwardLargePrimeCovariance_comm
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (m' : ℕ) (a b : ℕ × ℕ) :
    taoBackwardLargePrimeCovariance P hP m' a b =
      taoBackwardLargePrimeCovariance P hP m' b a := by
  rw [taoBackwardLargePrimeCovariance, taoBackwardLargePrimeCovariance,
    taoBackwardLargePrimeJointProbability_comm]
  ring

def taoBackwardLargePrimeVariance
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (lowerPrime upperPrime H m' : ℕ) : ℝ :=
  taoBackwardLargePrimeSecondMoment P hP lowerPrime upperPrime H m' -
    taoBackwardLargePrimeMean P hP lowerPrime upperPrime H m' ^ (2 : ℕ)

theorem taoBackwardLargePrimeVariance_eq
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (lowerPrime upperPrime H m' : ℕ) :
    taoBackwardLargePrimeVariance P hP lowerPrime upperPrime H m' =
      ∑ a ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H,
        ∑ b ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H,
          taoBackwardLargePrimeCovariance P hP m' a b := by
  rw [taoBackwardLargePrimeVariance, taoBackwardLargePrimeSecondMoment_eq,
    taoBackwardLargePrimeMean_eq, pow_two, Finset.sum_mul_sum]
  simp only [taoBackwardLargePrimeCovariance,
    taoBackwardLargePrimeJointProbability,
    taoBackwardLargePrimeProbability, Finset.sum_sub_distrib]

theorem natModEq_iff_dvd_add_sub
    {n l p : ℕ} (hl : l ≤ p) :
    n ≡ l [MOD p] ↔ p ∣ n + (p - l) := by
  constructor
  · intro h
    have hadd := h.add_right (p - l)
    have hpZero : p ≡ 0 [MOD p] :=
      Nat.modEq_zero_iff_dvd.mpr (dvd_refl p)
    apply Nat.modEq_zero_iff_dvd.mp
    have hadd' : n + (p - l) ≡ p [MOD p] := by
      simpa [Nat.add_sub_of_le hl] using hadd
    exact hadd'.trans hpZero
  · intro h
    have hnZero : n + (p - l) ≡ 0 [MOD p] :=
      Nat.modEq_zero_iff_dvd.mpr h
    have hlZero : l + (p - l) ≡ 0 [MOD p] := by
      rw [Nat.add_sub_of_le hl]
      exact Nat.modEq_zero_iff_dvd.mpr (dvd_refl p)
    exact Nat.ModEq.add_right_cancel' (p - l) (hnZero.trans hlZero.symm)

/-- The forward shift encoding of the backward residue `v ≡ l (mod p)`. -/
def taoBackwardReflectedShift (a : ℕ × ℕ) : ℕ × ℕ :=
  (a.2 - a.1, a.2)

theorem taoBackwardLargePrimeDivisibilityEvent_iff_reflected
    {m' : ℕ} {a : ℕ × ℕ} {ω : TaoPrimeTuple} (hl : a.1 ≤ a.2) :
    TaoBackwardLargePrimeDivisibilityEvent m' a ω ↔
      TaoLargePrimeDivisibilityEvent m' (taoBackwardReflectedShift a) ω := by
  rw [TaoBackwardLargePrimeDivisibilityEvent,
    TaoLargePrimeDivisibilityEvent, taoBackwardReflectedShift]
  exact natModEq_iff_dvd_add_sub hl

theorem taoBackwardLargePrimeProbability_eq_reflected
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (m' : ℕ) {a : ℕ × ℕ} (hl : a.1 ≤ a.2) :
    taoBackwardLargePrimeProbability P hP m' a =
      taoLargePrimeProbability P hP m' (taoBackwardReflectedShift a) := by
  unfold taoBackwardLargePrimeProbability taoLargePrimeProbability
  congr 2
  ext ω
  exact taoBackwardLargePrimeDivisibilityEvent_iff_reflected hl

theorem taoBackwardLargePrimeJointProbability_eq_reflected
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (m' : ℕ) {a b : ℕ × ℕ} (ha : a.1 ≤ a.2) (hb : b.1 ≤ b.2) :
    taoBackwardLargePrimeJointProbability P hP m' a b =
      taoLargePrimeJointProbability P hP m'
        (taoBackwardReflectedShift a) (taoBackwardReflectedShift b) := by
  unfold taoBackwardLargePrimeJointProbability taoLargePrimeJointProbability
  congr 2
  ext ω
  simp only [TaoBackwardLargePrimeJointDivisibilityEvent,
    TaoLargePrimeJointDivisibilityEvent]
  rw [taoBackwardLargePrimeDivisibilityEvent_iff_reflected ha,
    taoBackwardLargePrimeDivisibilityEvent_iff_reflected hb]

theorem taoBackwardLargePrimeCovariance_eq_reflected
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (m' : ℕ) {a b : ℕ × ℕ} (ha : a.1 ≤ a.2) (hb : b.1 ≤ b.2) :
    taoBackwardLargePrimeCovariance P hP m' a b =
      taoLargePrimeCovariance P hP m'
        (taoBackwardReflectedShift a) (taoBackwardReflectedShift b) := by
  rw [taoBackwardLargePrimeCovariance, taoLargePrimeCovariance,
    taoBackwardLargePrimeJointProbability_eq_reflected P hP m' ha hb,
    taoBackwardLargePrimeProbability_eq_reflected P hP m' ha,
    taoBackwardLargePrimeProbability_eq_reflected P hP m' hb]

theorem taoBackwardReflectedShift_second (a : ℕ × ℕ) :
    (taoBackwardReflectedShift a).2 = a.2 := rfl

theorem taoBackwardReflectedShift_first_pos
    {a : ℕ × ℕ} (h : a.1 < a.2) :
    0 < (taoBackwardReflectedShift a).1 := by
  simp only [taoBackwardReflectedShift]
  omega

theorem taoBackwardReflectedShift_first_lt
    {a : ℕ × ℕ} (hpos : 0 < a.1) (hlt : a.1 < a.2) :
    (taoBackwardReflectedShift a).1 < a.2 := by
  simp only [taoBackwardReflectedShift]
  omega

theorem taoBackwardReflectedShift_not_dvd
    {a : ℕ × ℕ} (hpos : 0 < a.1) (hlt : a.1 < a.2) :
    ¬(taoBackwardReflectedShift a).2 ∣
      (taoBackwardReflectedShift a).1 := by
  rw [taoBackwardReflectedShift_second]
  exact Nat.not_dvd_of_pos_of_lt
    (taoBackwardReflectedShift_first_pos hlt)
    (taoBackwardReflectedShift_first_lt hpos hlt)

theorem taoBackwardLargePrimeProbability_nonneg
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (m' : ℕ) (a : ℕ × ℕ) :
    0 ≤ taoBackwardLargePrimeProbability P hP m' a :=
  measureReal_nonneg

theorem taoBackwardLargePrimeProbability_eq_zero_of_dvd_base
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    {m' : ℕ} {a : ℕ × ℕ} (hpos : 0 < a.1) (hlt : a.1 < a.2)
    (hm : a.2 ∣ m') :
    taoBackwardLargePrimeProbability P hP m' a = 0 := by
  rw [taoBackwardLargePrimeProbability_eq_reflected P hP m' hlt.le]
  exact taoLargePrimeProbability_eq_zero_of_dvd_base P hP hm
    (taoBackwardReflectedShift_not_dvd hpos hlt)

theorem taoBackwardLargePrimeCovariance_eq_zero_of_left_dvd_base
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    {m' : ℕ} {a b : ℕ × ℕ}
    (hapos : 0 < a.1) (halt : a.1 < a.2) (hm : a.2 ∣ m') :
    taoBackwardLargePrimeCovariance P hP m' a b = 0 := by
  rw [taoBackwardLargePrimeCovariance,
    taoBackwardLargePrimeProbability_eq_zero_of_dvd_base
      P hP hapos halt hm]
  have hjoint : taoBackwardLargePrimeJointProbability P hP m' a b = 0 := by
    unfold taoBackwardLargePrimeJointProbability
    rw [show {ω : TaoPrimeTuple |
        TaoBackwardLargePrimeJointDivisibilityEvent m' a b ω} = ∅ by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hω
      have hstart : a.2 ∣ taoPrimeTupleStart m' ω := by
        unfold taoPrimeTupleStart
        exact dvd_mul_of_dvd_right hm _
      have hlzero : a.1 ≡ 0 [MOD a.2] :=
        hω.1.symm.trans hstart.modEq_zero_nat
      exact (Nat.not_dvd_of_pos_of_lt hapos halt)
        (Nat.modEq_zero_iff_dvd.mp hlzero)]
    exact measureReal_empty
  rw [hjoint]
  ring

theorem taoBackwardLargePrimeCovariance_eq_zero_of_right_dvd_base
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    {m' : ℕ} {a b : ℕ × ℕ}
    (hbpos : 0 < b.1) (hblt : b.1 < b.2) (hm : b.2 ∣ m') :
    taoBackwardLargePrimeCovariance P hP m' a b = 0 := by
  rw [taoBackwardLargePrimeCovariance_comm P hP m' a b]
  exact taoBackwardLargePrimeCovariance_eq_zero_of_left_dvd_base
    P hP hbpos hblt hm

theorem taoBackwardLargePrimeCovariance_le_jointProbability
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (m' : ℕ) (a b : ℕ × ℕ) :
    taoBackwardLargePrimeCovariance P hP m' a b ≤
      taoBackwardLargePrimeJointProbability P hP m' a b := by
  rw [taoBackwardLargePrimeCovariance]
  nlinarith [mul_nonneg
    (taoBackwardLargePrimeProbability_nonneg P hP m' a)
    (taoBackwardLargePrimeProbability_nonneg P hP m' b)]

theorem taoBackwardLargePrimeJointProbability_self
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (m' : ℕ) (a : ℕ × ℕ) :
    taoBackwardLargePrimeJointProbability P hP m' a a =
      taoBackwardLargePrimeProbability P hP m' a := by
  unfold taoBackwardLargePrimeJointProbability
    taoBackwardLargePrimeProbability
  congr 2
  ext ω
  simp [TaoBackwardLargePrimeJointDivisibilityEvent]

theorem taoBackwardLargePrimeCovariance_self_le_probability
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (m' : ℕ) (a : ℕ × ℕ) :
    taoBackwardLargePrimeCovariance P hP m' a a ≤
      taoBackwardLargePrimeProbability P hP m' a := by
  rw [taoBackwardLargePrimeCovariance,
    taoBackwardLargePrimeJointProbability_self]
  nlinarith [sq_nonneg (taoBackwardLargePrimeProbability P hP m' a)]

theorem taoBackwardLargePrimeJointDivisibilityEvent_empty_of_same_prime
    {lowerPrime upperPrime H m' : ℕ} {a b : ℕ × ℕ}
    (haMem : a ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H)
    (hbMem : b ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H)
    (hH : H ≤ lowerPrime) (hp : a.2 = b.2) (hl : a.1 ≠ b.1) :
    {ω : TaoPrimeTuple |
      TaoBackwardLargePrimeJointDivisibilityEvent m' a b ω} = ∅ := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨ha, hb⟩
  have hshifts : a.1 ≡ b.1 [MOD a.2] :=
    ha.symm.trans (by simpa [hp] using hb)
  have haData := mem_taoLargeAntiSieveIndices.mp haMem
  have hbData := mem_taoLargeAntiSieveIndices.mp hbMem
  have haLt : a.1 < a.2 :=
    lt_of_lt_of_le haData.2.1
      (le_trans hH (Nat.le_of_lt haData.2.2.2.1))
  have hbLt : b.1 < a.2 := by
    have hbPrimeLt : lowerPrime < a.2 := by
      simpa [hp] using hbData.2.2.2.1
    exact lt_of_lt_of_le hbData.2.1
      (le_trans hH (Nat.le_of_lt hbPrimeLt))
  exact hl (hshifts.eq_of_lt_of_lt haLt hbLt)

theorem taoBackwardLargePrimeJointProbability_eq_zero_of_same_prime
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    {lowerPrime upperPrime H m' : ℕ} {a b : ℕ × ℕ}
    (haMem : a ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H)
    (hbMem : b ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H)
    (hH : H ≤ lowerPrime) (hp : a.2 = b.2) (hl : a.1 ≠ b.1) :
    taoBackwardLargePrimeJointProbability P hP m' a b = 0 := by
  rw [taoBackwardLargePrimeJointProbability,
    taoBackwardLargePrimeJointDivisibilityEvent_empty_of_same_prime
      haMem hbMem hH hp hl]
  exact measureReal_empty

theorem taoBackwardLargePrimeCovariance_nonpos_of_same_prime
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    {lowerPrime upperPrime H m' : ℕ} {a b : ℕ × ℕ}
    (haMem : a ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H)
    (hbMem : b ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H)
    (hH : H ≤ lowerPrime) (hp : a.2 = b.2) (hl : a.1 ≠ b.1) :
    taoBackwardLargePrimeCovariance P hP m' a b ≤ 0 := by
  rw [taoBackwardLargePrimeCovariance,
    taoBackwardLargePrimeJointProbability_eq_zero_of_same_prime
      P hP haMem hbMem hH hp hl]
  simpa only [zero_sub] using neg_nonpos.mpr (mul_nonneg
    (taoBackwardLargePrimeProbability_nonneg P hP m' a)
    (taoBackwardLargePrimeProbability_nonneg P hP m' b))

theorem sum_taoBackwardLargePrimeCovariance_le_probability_add_distinctPrimes
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    {lowerPrime upperPrime H m' : ℕ} {a : ℕ × ℕ}
    (haMem : a ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H)
    (hH : H ≤ lowerPrime) :
    (∑ b ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H,
      taoBackwardLargePrimeCovariance P hP m' a b) ≤
      taoBackwardLargePrimeProbability P hP m' a +
        ∑ b ∈ (taoLargeAntiSieveIndices lowerPrime upperPrime H).filter
          (fun b => b.2 ≠ a.2),
            taoBackwardLargePrimeCovariance P hP m' a b := by
  let S := taoLargeAntiSieveIndices lowerPrime upperPrime H
  let same := S.filter fun b => b.2 = a.2
  have haSame : a ∈ same := by simp [same, S, haMem]
  have hsame :
      (∑ b ∈ same, taoBackwardLargePrimeCovariance P hP m' a b) ≤
        taoBackwardLargePrimeProbability P hP m' a := by
    rw [Finset.sum_eq_add_sum_diff_singleton_of_mem haSame]
    calc
      taoBackwardLargePrimeCovariance P hP m' a a +
          ∑ b ∈ same \ {a},
            taoBackwardLargePrimeCovariance P hP m' a b ≤
        taoBackwardLargePrimeProbability P hP m' a + 0 := by
          apply add_le_add
            (taoBackwardLargePrimeCovariance_self_le_probability P hP m' a)
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
          exact taoBackwardLargePrimeCovariance_nonpos_of_same_prime
            P hP (by simpa [S] using haMem) (by simpa [S] using hbMem)
              hH hp hl
      _ = taoBackwardLargePrimeProbability P hP m' a := add_zero _
  calc
    (∑ b ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H,
        taoBackwardLargePrimeCovariance P hP m' a b) =
      (∑ b ∈ same, taoBackwardLargePrimeCovariance P hP m' a b) +
        ∑ b ∈ S.filter (fun b => ¬b.2 = a.2),
          taoBackwardLargePrimeCovariance P hP m' a b := by
            rw [← Finset.sum_filter_add_sum_filter_not S
              (fun b => b.2 = a.2)]
    _ ≤ taoBackwardLargePrimeProbability P hP m' a +
        ∑ b ∈ S.filter (fun b => ¬b.2 = a.2),
          taoBackwardLargePrimeCovariance P hP m' a b :=
      add_le_add hsame (le_refl _)
    _ = taoBackwardLargePrimeProbability P hP m' a +
        ∑ b ∈ (taoLargeAntiSieveIndices lowerPrime upperPrime H).filter
          (fun b => b.2 ≠ a.2),
            taoBackwardLargePrimeCovariance P hP m' a b := by rfl

theorem taoBackwardLargePrimeVariance_le_mean_add_distinctPrimeCovariances
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (lowerPrime upperPrime H m' : ℕ) (hH : H ≤ lowerPrime) :
    taoBackwardLargePrimeVariance P hP lowerPrime upperPrime H m' ≤
      taoBackwardLargePrimeMean P hP lowerPrime upperPrime H m' +
        ∑ a ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H,
          ∑ b ∈ (taoLargeAntiSieveIndices lowerPrime upperPrime H).filter
            (fun b => b.2 ≠ a.2),
              taoBackwardLargePrimeCovariance P hP m' a b := by
  rw [taoBackwardLargePrimeVariance_eq, taoBackwardLargePrimeMean_eq]
  calc
    (∑ a ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H,
        ∑ b ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H,
          taoBackwardLargePrimeCovariance P hP m' a b) ≤
      ∑ a ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H,
        ((taoPrimeTupleMeasure P hP).real
            {w | TaoBackwardLargePrimeDivisibilityEvent m' a w} +
          ∑ b ∈ (taoLargeAntiSieveIndices lowerPrime upperPrime H).filter
            (fun b => b.2 ≠ a.2),
              taoBackwardLargePrimeCovariance P hP m' a b) := by
        apply Finset.sum_le_sum
        intro a ha
        exact sum_taoBackwardLargePrimeCovariance_le_probability_add_distinctPrimes
          P hP ha hH
    _ = (∑ a ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H,
          (taoPrimeTupleMeasure P hP).real
            {w | TaoBackwardLargePrimeDivisibilityEvent m' a w}) +
        ∑ a ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H,
          ∑ b ∈ (taoLargeAntiSieveIndices lowerPrime upperPrime H).filter
            (fun b => b.2 ≠ a.2),
              taoBackwardLargePrimeCovariance P hP m' a b := by
      rw [Finset.sum_add_distrib]

/-- Reflected one-prime adaptive estimate; only the residue has changed. -/
theorem taoBackwardLargePrimeProbability_le_main_add_adaptiveError
    {D : Finset ℕ} {m' R : ℕ} (a : ℕ × ℕ)
    (hp : Nat.Prime a.2) (hpD : a.2 ∈ D)
    (hpos : 0 < a.1) (hlt : a.1 < a.2) (hm : Nat.Coprime m' a.2)
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (hpExceptional :
      a.2 ∉ taoLargePrimeAdaptiveExceptionalConductorsFor D P R) :
    taoBackwardLargePrimeProbability P hP m' a ≤
      1 / (a.2.totient : ℝ) +
        taoLargePrimeAdaptiveImprovedError P a.2 R := by
  rw [taoBackwardLargePrimeProbability_eq_reflected P hP m' hlt.le]
  simpa only [taoBackwardReflectedShift_second] using
    taoLargePrimeProbability_le_main_add_adaptiveError
      (taoBackwardReflectedShift a) hp hpD
      (taoBackwardReflectedShift_not_dvd hpos hlt) hm P hP hpExceptional

theorem taoBackwardLargePrimeCovariance_le_mixedAdaptiveErrors
    {m' R S : ℕ} (a b : ℕ × ℕ)
    (hp : Nat.Prime a.2) (hq : Nat.Prime b.2) (hpq : a.2 ≠ b.2)
    (hapos : 0 < a.1) (halt : a.1 < a.2)
    (hbpos : 0 < b.1) (hblt : b.1 < b.2)
    (hm : Nat.Coprime m' (a.2 * b.2))
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (hpair : TaoLargePrimeAdaptivePairUnexceptional P R S a b) :
    taoBackwardLargePrimeCovariance P hP m' a b ≤
      taoLargePrimeMixedAdaptiveCovarianceImprovedError P a.2 b.2 R S := by
  rw [taoBackwardLargePrimeCovariance_eq_reflected
    P hP m' halt.le hblt.le]
  have hpair' : TaoLargePrimeAdaptivePairUnexceptional P R S
      (taoBackwardReflectedShift a) (taoBackwardReflectedShift b) := by
    simpa only [TaoLargePrimeAdaptivePairUnexceptional,
      taoBackwardReflectedShift_second] using hpair
  simpa only [taoBackwardReflectedShift_second] using
    taoLargePrimeCovariance_le_mixedAdaptiveErrors
      (taoBackwardReflectedShift a) (taoBackwardReflectedShift b)
      hp hq hpq (taoBackwardReflectedShift_not_dvd hapos halt)
      (taoBackwardReflectedShift_not_dvd hbpos hblt) hm P hP hpair'

end

end Tao2026
