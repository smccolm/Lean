import Tao2026.BadIntervalTypicalAntiSieve
import Tao2026.BadIntervalBackwardProbabilityNormalization

/-!
# Backward typical intervals: deterministic anti-sieve

This is the right-endpoint `v-l` counterpart of the deterministic bridge in
Proposition 6.6.  Subtraction is confined to interval membership; all random
divisibility events use the equivalent congruence `v ≡ l (mod p)`.
-/

namespace Tao2026

open Filter Topology MeasureTheory
open scoped Classical BigOperators

noncomputable section

def taoBackwardExceptionalShiftPrimeWeight
    (m' l : ℕ) (ω : TaoPrimeTuple) : ℝ :=
  ∑ p ∈ l.primeFactors,
    taoBackwardPrimeDivisibilityIndicator m' l p ω * Real.log p

theorem taoBackwardExceptionalShiftPrimeWeight_le_log
    (m' : ℕ) {l : ℕ} (hl : 0 < l) (ω : TaoPrimeTuple) :
    taoBackwardExceptionalShiftPrimeWeight m' l ω ≤ Real.log l := by
  calc
    taoBackwardExceptionalShiftPrimeWeight m' l ω ≤
        ∑ p ∈ l.primeFactors, Real.log p := by
      apply Finset.sum_le_sum
      intro p hp
      have hpPrime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
      have hlog : 0 ≤ Real.log (p : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hpPrime.one_le)
      simpa using mul_le_mul_of_nonneg_right
        (taoBackwardPrimeDivisibilityIndicator_le_one m' l p ω) hlog
    _ ≤ Real.log l := sum_log_primeFactors_le_log hl

def taoBackwardExceptionalPrimeContribution
    (H m' : ℕ) (ω : TaoPrimeTuple) : ℝ :=
  ∑ l ∈ Finset.Ico 1 H, taoBackwardExceptionalShiftPrimeWeight m' l ω

theorem taoBackwardExceptionalPrimeContribution_le
    {H : ℕ} (hH : 1 ≤ H) (m' : ℕ) (ω : TaoPrimeTuple) :
    taoBackwardExceptionalPrimeContribution H m' ω ≤ H * Real.log H := by
  have hterm : ∀ l ∈ Finset.Ico 1 H,
      taoBackwardExceptionalShiftPrimeWeight m' l ω ≤ Real.log H := by
    intro l hl
    have hlData := Finset.mem_Ico.mp hl
    exact (taoBackwardExceptionalShiftPrimeWeight_le_log m' hlData.1 ω).trans
      (Real.log_le_log (by exact_mod_cast hlData.1)
        (by exact_mod_cast hlData.2.le))
  calc
    taoBackwardExceptionalPrimeContribution H m' ω ≤
        ∑ _l ∈ Finset.Ico 1 H, Real.log H := by
      exact Finset.sum_le_sum hterm
    _ = ((Finset.Ico 1 H).card : ℝ) * Real.log H := by simp
    _ ≤ H * Real.log H := by
      have hcard : ((Finset.Ico 1 H).card : ℝ) ≤ H := by
        exact_mod_cast (show (Finset.Ico 1 H).card ≤ H by
          rw [Nat.card_Ico]
          exact Nat.sub_le H 1)
      exact mul_le_mul_of_nonneg_right hcard
        (Real.log_nonneg (by exact_mod_cast hH))

theorem eventually_taoBackwardExceptionalPrimeContribution_le_log_taoZ :
    ∀ᶠ x : ℕ in atTop, ∀ H m' : ℕ, ∀ ω : TaoPrimeTuple,
      1 ≤ H → H ≤ taoTypicalLengthCutoff x →
        taoBackwardExceptionalPrimeContribution H m' ω ≤
          H * Real.log (taoZ x) := by
  filter_upwards [
    eventually_const_mul_taoTypicalLengthCutoff_le_taoZ_rpow
      (C := (1 : ℝ)) (δ := (1 : ℝ)) (by norm_num) (by norm_num)] with
      x hcutoff H m' ω hH hHcutoff
  have hcutoffZ : (taoTypicalLengthCutoff x : ℝ) ≤ taoZ x := by
    simpa using hcutoff
  have hHcutoffReal : (H : ℝ) ≤ taoTypicalLengthCutoff x := by
    exact_mod_cast hHcutoff
  have hHZ : (H : ℝ) ≤ taoZ x := hHcutoffReal.trans hcutoffZ
  have hlog : Real.log (H : ℝ) ≤ Real.log (taoZ x) :=
    Real.log_le_log (by exact_mod_cast hH) hHZ
  exact (taoBackwardExceptionalPrimeContribution_le hH m' ω).trans
    (mul_le_mul_of_nonneg_left hlog (by positivity))

def TaoBackwardExceptionalPrimeLargeEvent
    (x H m' : ℕ) (ω : TaoPrimeTuple) : Prop :=
  H * Real.log (taoZ x) < taoBackwardExceptionalPrimeContribution H m' ω

theorem eventually_taoBackwardExceptionalPrimeLargeEvent_eq_empty :
    ∀ᶠ x : ℕ in atTop, ∀ H m' : ℕ,
      1 ≤ H → H ≤ taoTypicalLengthCutoff x →
        {ω : TaoPrimeTuple | TaoBackwardExceptionalPrimeLargeEvent x H m' ω} = ∅ := by
  filter_upwards [
    eventually_taoBackwardExceptionalPrimeContribution_le_log_taoZ] with
      x hx H m' hH hHcutoff
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  exact not_lt_of_ge (hx H m' ω hH hHcutoff)

def taoBackwardLargePrimeLogContribution
    (lowerPrime upperPrime H m' : ℕ) (ω : TaoPrimeTuple) : ℝ :=
  ∑ lp ∈ taoLargeAntiSieveIndices lowerPrime upperPrime H,
    taoBackwardPrimeDivisibilityIndicator m' lp.1 lp.2 ω * Real.log lp.2

theorem taoBackwardLargePrimeLogContribution_le_log_mul
    (lowerPrime upperPrime H m' : ℕ) (ω : TaoPrimeTuple) :
    taoBackwardLargePrimeLogContribution lowerPrime upperPrime H m' ω ≤
      Real.log upperPrime *
        taoBackwardLargePrimeContribution lowerPrime upperPrime H m' ω := by
  unfold taoBackwardLargePrimeLogContribution taoBackwardLargePrimeContribution
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
    taoBackwardPrimeDivisibilityIndicator m' lp.1 lp.2 ω * Real.log lp.2 ≤
        taoBackwardPrimeDivisibilityIndicator m' lp.1 lp.2 ω *
          Real.log upperPrime :=
      mul_le_mul_of_nonneg_left hlog
        (taoBackwardPrimeDivisibilityIndicator_nonneg _ _ _ _)
    _ = Real.log upperPrime *
        taoBackwardPrimeDivisibilityIndicator m' lp.1 lp.2 ω := by ring

def taoBackwardSmallPrimeContributionAtShift
    (x l m' : ℕ) (ω : TaoPrimeTuple) : ℝ :=
  ∑ p ∈ (taoSmallAntiSievePrimeRange x).filter (fun p => ¬p ∣ l),
    taoBackwardPrimeDivisibilityIndicator m' l p ω * Real.log p

def taoBackwardLargePrimeLogContributionAtShift
    (lowerPrime upperPrime l m' : ℕ) (ω : TaoPrimeTuple) : ℝ :=
  ∑ p ∈ taoLargeAntiSievePrimeRange lowerPrime upperPrime,
    taoBackwardPrimeDivisibilityIndicator m' l p ω * Real.log p

theorem sum_taoBackwardSmallPrimeContributionAtShift_eq
    (x H m' : ℕ) (ω : TaoPrimeTuple) :
    (∑ l ∈ Finset.Ico 1 H,
        taoBackwardSmallPrimeContributionAtShift x l m' ω) =
      taoBackwardSmallPrimeContribution x H m' ω := by
  unfold taoBackwardSmallPrimeContributionAtShift
    taoBackwardSmallPrimeContribution taoBackwardSmallAntiSieveTerm
    taoSmallAntiSieveIndices
  rw [show
      (∑ lp ∈ ((Finset.Ico 1 H).product
          (taoSmallAntiSievePrimeRange x)).filter (fun lp => ¬lp.2 ∣ lp.1),
        taoBackwardPrimeDivisibilityIndicator m' lp.1 lp.2 ω * Real.log lp.2) =
        ∑ l ∈ Finset.Ico 1 H,
          ∑ p ∈ (taoSmallAntiSievePrimeRange x).filter (fun p => ¬p ∣ l),
            taoBackwardPrimeDivisibilityIndicator m' l p ω * Real.log p by
    rw [Finset.sum_filter]
    simp_rw [Finset.sum_filter]
    exact Finset.sum_product _ _ _]

theorem sum_taoBackwardLargePrimeLogContributionAtShift_eq
    (lowerPrime upperPrime H m' : ℕ) (ω : TaoPrimeTuple) :
    (∑ l ∈ Finset.Ico 1 H,
        taoBackwardLargePrimeLogContributionAtShift lowerPrime upperPrime l m' ω) =
      taoBackwardLargePrimeLogContribution lowerPrime upperPrime H m' ω := by
  unfold taoBackwardLargePrimeLogContributionAtShift
    taoBackwardLargePrimeLogContribution taoLargeAntiSieveIndices
  exact (Finset.sum_product (Finset.Ico 1 H)
    (taoLargeAntiSievePrimeRange lowerPrime upperPrime)
    (fun lp : ℕ × ℕ =>
      taoBackwardPrimeDivisibilityIndicator m' lp.1 lp.2 ω * Real.log lp.2)).symm

theorem sum_log_primeFactors_squarefreeComponent_sub_le_three_shift_contributions
    {x l upperPrime m' : ℕ} {ω : TaoPrimeTuple}
    (hl : 0 < l) (hlt : l < taoPrimeTupleStart m' ω)
    (hsmooth : IsSmooth (taoPrimeTupleStart m' ω - l) upperPrime) :
    (∑ p ∈ (squarefreeComponent
          (taoPrimeTupleStart m' ω - l)).primeFactors, Real.log p) ≤
      taoBackwardExceptionalShiftPrimeWeight m' l ω +
        taoBackwardSmallPrimeContributionAtShift x l m' ω +
          taoBackwardLargePrimeLogContributionAtShift
            (taoSmallAntiSievePrimeCutoff x) upperPrime l m' ω := by
  let n : ℕ := taoPrimeTupleStart m' ω - l
  let F : Finset ℕ := (squarefreeComponent n).primeFactors
  let E : Finset ℕ := l.primeFactors
  let S : Finset ℕ :=
    (taoSmallAntiSievePrimeRange x).filter (fun p => ¬p ∣ l)
  let L : Finset ℕ :=
    taoLargeAntiSievePrimeRange (taoSmallAntiSievePrimeCutoff x) upperPrime
  let f : ℕ → ℝ := fun p =>
    if p.Prime then
      taoBackwardPrimeDivisibilityIndicator m' l p ω * Real.log p
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
          taoBackwardPrimeDivisibilityIndicator m' l p ω * Real.log p else 0
      rw [if_pos hp]
      exact mul_nonneg (taoBackwardPrimeDivisibilityIndicator_nonneg _ _ _ _)
        (Real.log_nonneg (by exact_mod_cast hp.one_le))
    · simp [f, hp]
  have hfactorEq :
      (∑ p ∈ F, Real.log p) = ∑ p ∈ F, f p := by
    apply Finset.sum_congr rfl
    intro p hp
    have hpPrime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    have hpComponentDvd : p ∣ squarefreeComponent n :=
      Nat.dvd_of_mem_primeFactors hp
    have hpN : p ∣ taoPrimeTupleStart m' ω - l := by
      simpa only [n] using
        dvd_trans hpComponentDvd (squarefreeComponent_dvd n)
    have hmod : taoPrimeTupleStart m' ω ≡ l [MOD p] := by
      exact ((Nat.modEq_iff_dvd' (Nat.le_of_lt hlt)).2 hpN).symm
    simp [f, hpPrime, taoBackwardPrimeDivisibilityIndicator, hmod]
  have hEeq : (∑ p ∈ E, f p) =
      taoBackwardExceptionalShiftPrimeWeight m' l ω := by
    unfold taoBackwardExceptionalShiftPrimeWeight
    apply Finset.sum_congr rfl
    intro p hp
    have hpPrime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
    simp [f, hpPrime]
  have hSeq : (∑ p ∈ S, f p) =
      taoBackwardSmallPrimeContributionAtShift x l m' ω := by
    unfold taoBackwardSmallPrimeContributionAtShift
    apply Finset.sum_congr rfl
    intro p hp
    have hpPrime : Nat.Prime p :=
      (mem_taoSmallAntiSievePrimeRange.mp (Finset.mem_filter.mp hp).1).1
    simp [f, hpPrime]
  have hLeq : (∑ p ∈ L, f p) =
      taoBackwardLargePrimeLogContributionAtShift
        (taoSmallAntiSievePrimeCutoff x) upperPrime l m' ω := by
    unfold taoBackwardLargePrimeLogContributionAtShift
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
    _ = taoBackwardExceptionalShiftPrimeWeight m' l ω +
        taoBackwardSmallPrimeContributionAtShift x l m' ω +
          taoBackwardLargePrimeLogContributionAtShift
            (taoSmallAntiSievePrimeCutoff x) upperPrime l m' ω := by
      rw [hEeq, hSeq, hLeq]

theorem sum_squarefreePrimeLogs_sub_le_three_contributions
    {x H upperPrime m' : ℕ} {ω : TaoPrimeTuple}
    (hlt : ∀ l ∈ Finset.Ico 1 H, l < taoPrimeTupleStart m' ω)
    (hsmooth : ∀ l ∈ Finset.Ico 1 H,
      IsSmooth (taoPrimeTupleStart m' ω - l) upperPrime) :
    (∑ l ∈ Finset.Ico 1 H,
        ∑ p ∈ (squarefreeComponent
          (taoPrimeTupleStart m' ω - l)).primeFactors, Real.log p) ≤
      taoBackwardExceptionalPrimeContribution H m' ω +
        taoBackwardSmallPrimeContribution x H m' ω +
          taoBackwardLargePrimeLogContribution
            (taoSmallAntiSievePrimeCutoff x) upperPrime H m' ω := by
  calc
    (∑ l ∈ Finset.Ico 1 H,
        ∑ p ∈ (squarefreeComponent
          (taoPrimeTupleStart m' ω - l)).primeFactors, Real.log p) ≤
      ∑ l ∈ Finset.Ico 1 H,
        (taoBackwardExceptionalShiftPrimeWeight m' l ω +
          taoBackwardSmallPrimeContributionAtShift x l m' ω +
            taoBackwardLargePrimeLogContributionAtShift
              (taoSmallAntiSievePrimeCutoff x) upperPrime l m' ω) := by
      apply Finset.sum_le_sum
      intro l hl
      exact sum_log_primeFactors_squarefreeComponent_sub_le_three_shift_contributions
        (Finset.mem_Ico.mp hl).1 (hlt l hl) (hsmooth l hl)
    _ = taoBackwardExceptionalPrimeContribution H m' ω +
        taoBackwardSmallPrimeContribution x H m' ω +
          taoBackwardLargePrimeLogContribution
            (taoSmallAntiSievePrimeCutoff x) upperPrime H m' ω := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        sum_taoBackwardSmallPrimeContributionAtShift_eq,
        sum_taoBackwardLargePrimeLogContributionAtShift_eq]
      rfl

theorem TaoPrimeTupleBackwardTypicalEvent.sum_squarefreePrimeLogs_lower
    {x H lowerPrime upperPrime m' : ℕ} {ω : TaoPrimeTuple}
    (hx : 0 < x)
    (htypical : TaoPrimeTupleBackwardTypicalEvent
      x H lowerPrime upperPrime m' ω) :
    ((H - 1 : ℕ) : ℝ) *
        (Real.log x - Real.log 4 -
          2 * Real.log (taoTypicalSquareThreshold x)) ≤
      ∑ l ∈ Finset.Ico 1 H,
        ∑ p ∈ (squarefreeComponent
          (taoPrimeTupleStart m' ω - l)).primeFactors, Real.log p := by
  rw [TaoPrimeTupleBackwardTypicalEvent,
    IsBackwardTypicalScaleNormalizedBadInterval,
    IsTypicalScaleNormalizedBadInterval,
    SatisfiesTypicalNormalizedConditions] at htypical
  obtain ⟨⟨hnorm, hleft, _hright, _hlength, havoid, _hanatomy⟩,
    hstart⟩ := htypical
  have hpoint : ∀ l ∈ Finset.Ico 1 H,
      Real.log x - Real.log 4 -
          2 * Real.log (taoTypicalSquareThreshold x) ≤
        ∑ p ∈ (squarefreeComponent
          (taoPrimeTupleStart m' ω - l)).primeFactors, Real.log p := by
    intro l hl
    have hlData := Finset.mem_Ico.mp hl
    have hlt : l < taoPrimeTupleStart m' ω := by omega
    have hnmem : taoPrimeTupleStart m' ω - l ∈
        consecutiveInterval (taoPrimeTupleStart m' ω - H) H := by
      rw [consecutiveInterval, Finset.mem_Ioc]
      omega
    calc
      Real.log x - Real.log 4 -
          2 * Real.log (taoTypicalSquareThreshold x) ≤
        Real.log (squarefreeComponent
          (taoPrimeTupleStart m' ω - l)) :=
        log_squarefreeComponent_lower_of_avoids hx
          (taoTypicalSquareThreshold_pos x) hleft hnmem havoid
      _ = ∑ p ∈ (squarefreeComponent
          (taoPrimeTupleStart m' ω - l)).primeFactors, Real.log p :=
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
          (taoPrimeTupleStart m' ω - l)).primeFactors, Real.log p := by
      exact Finset.sum_le_sum hpoint

theorem TaoPrimeTupleBackwardTypicalEvent.sum_squarefreePrimeLogs_le_three_contributions
    {x H lowerPrime upperPrime m' : ℕ} {ω : TaoPrimeTuple}
    (htypical : TaoPrimeTupleBackwardTypicalEvent
      x H lowerPrime upperPrime m' ω) :
    (∑ l ∈ Finset.Ico 1 H,
        ∑ p ∈ (squarefreeComponent
          (taoPrimeTupleStart m' ω - l)).primeFactors, Real.log p) ≤
      taoBackwardExceptionalPrimeContribution H m' ω +
        taoBackwardSmallPrimeContribution x H m' ω +
          taoBackwardLargePrimeLogContribution
            (taoSmallAntiSievePrimeCutoff x) upperPrime H m' ω := by
  rw [TaoPrimeTupleBackwardTypicalEvent,
    IsBackwardTypicalScaleNormalizedBadInterval,
    IsTypicalScaleNormalizedBadInterval,
    SatisfiesTypicalNormalizedConditions] at htypical
  obtain ⟨⟨hnorm, _hleft, _hright, _hlength, _havoid, hanatomy⟩,
    hstart⟩ := htypical
  let anatomy : TypicalPrimeAnatomy lowerPrime upperPrime (ω 0)
      (taoPrimeTupleTailProduct ω * m') := Classical.choice hanatomy
  have hpUpper : ω 0 ≤ upperPrime := anatomy.p₀_le_upper
  apply Tao2026.sum_squarefreePrimeLogs_sub_le_three_contributions
  · intro l hl
    have hlData := Finset.mem_Ico.mp hl
    omega
  · intro l hl
    have hlData := Finset.mem_Ico.mp hl
    have hnmem : taoPrimeTupleStart m' ω - l ∈
        consecutiveInterval (taoPrimeTupleStart m' ω - H) H := by
      rw [consecutiveInterval, Finset.mem_Ioc]
      omega
    have hsmooth := hnorm.isSmooth_of_mem hnmem
    rw [isSmooth_iff] at hsmooth ⊢
    exact ⟨hsmooth.1, fun p hp hpdiv =>
      (hsmooth.2 p hp hpdiv).trans hpUpper⟩

theorem TaoPrimeTupleBackwardTypicalEvent.three_contributions_lower
    {x H lowerPrime upperPrime m' : ℕ} {ω : TaoPrimeTuple}
    (hx : 0 < x)
    (htypical : TaoPrimeTupleBackwardTypicalEvent
      x H lowerPrime upperPrime m' ω) :
    ((H - 1 : ℕ) : ℝ) *
        (Real.log x - Real.log 4 -
          2 * Real.log (taoTypicalSquareThreshold x)) ≤
      taoBackwardExceptionalPrimeContribution H m' ω +
        taoBackwardSmallPrimeContribution x H m' ω +
          Real.log upperPrime *
            taoBackwardLargePrimeContribution
              (taoSmallAntiSievePrimeCutoff x) upperPrime H m' ω := by
  calc
    ((H - 1 : ℕ) : ℝ) *
        (Real.log x - Real.log 4 -
          2 * Real.log (taoTypicalSquareThreshold x)) ≤
      ∑ l ∈ Finset.Ico 1 H,
        ∑ p ∈ (squarefreeComponent
          (taoPrimeTupleStart m' ω - l)).primeFactors, Real.log p :=
      htypical.sum_squarefreePrimeLogs_lower hx
    _ ≤ taoBackwardExceptionalPrimeContribution H m' ω +
        taoBackwardSmallPrimeContribution x H m' ω +
          taoBackwardLargePrimeLogContribution
            (taoSmallAntiSievePrimeCutoff x) upperPrime H m' ω :=
      htypical.sum_squarefreePrimeLogs_le_three_contributions
    _ ≤ taoBackwardExceptionalPrimeContribution H m' ω +
        taoBackwardSmallPrimeContribution x H m' ω +
          Real.log upperPrime *
            taoBackwardLargePrimeContribution
              (taoSmallAntiSievePrimeCutoff x) upperPrime H m' ω := by
      gcongr
      exact taoBackwardLargePrimeLogContribution_le_log_mul
        (taoSmallAntiSievePrimeCutoff x) upperPrime H m' ω

def TaoBackwardSourceAntiSieveLargeEvent
    (x H m' : ℕ) (ω : TaoPrimeTuple) : Prop :=
  TaoBackwardExceptionalPrimeLargeEvent x H m' ω ∨
    (H : ℝ) * Real.log (taoZ x) ^ (2 : ℕ) /
        (8 * iteratedLog x) <
      taoBackwardSmallPrimeContribution x H m' ω ∨
    2000000 * (H : ℝ) +
        (H : ℝ) * Real.log (taoZ x) / (8 * iteratedLog x) <
      taoBackwardLargePrimeContribution
        (taoLargePrimeSourceLowerCutoff x)
        (taoLargePrimeSourceUpperCutoff x) H m' ω

/-- Every backward source-scale typical tuple eventually lies in one of the
three backward anti-sieve large-deviation events. -/
theorem eventually_taoPrimeTupleBackwardTypicalEvent_imp_taoBackwardSourceAntiSieveLargeEvent :
    ∀ᶠ x : ℕ in atTop, ∀ H lowerPrime m' : ℕ, ∀ ω : TaoPrimeTuple,
      TaoPrimeTupleBackwardTypicalEvent x H lowerPrime
          (taoLargePrimeSourceUpperCutoff x) m' ω →
        TaoBackwardSourceAntiSieveLargeEvent x H m' ω := by
  filter_upwards [eventually_taoSourceAntiSieve_scalar_gap,
    eventually_gt_atTop (0 : ℕ)] with x hgap hx H lowerPrime m' ω htypical
  have htypicalData := htypical
  rw [TaoPrimeTupleBackwardTypicalEvent,
    IsBackwardTypicalScaleNormalizedBadInterval,
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
  let E : ℝ := taoBackwardExceptionalPrimeContribution H m' ω
  let S : ℝ := taoBackwardSmallPrimeContribution x H m' ω
  let X : ℝ := taoBackwardLargePrimeContribution
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
  simp only [TaoBackwardSourceAntiSieveLargeEvent, not_or, not_lt,
    TaoBackwardExceptionalPrimeLargeEvent] at hnotData
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

/-- Union-bound closure of the three backward anti-sieve branches. -/
theorem eventually_measureReal_taoBackwardSourceAntiSieveLargeEvent_le_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty)
    (H m' : ℕ → ℕ)
    (hH : ∀ᶠ x : ℕ in atTop, H x ≤ taoTypicalLengthCutoff x)
    (hHpos : ∀ᶠ x : ℕ in atTop, 1 ≤ H x) :
    ∀ᶠ x : ℕ in atTop,
      (taoPrimeTupleMeasure (P x) (hP x)).real
          {ω | TaoBackwardSourceAntiSieveLargeEvent x (H x) (m' x) ω} ≤
        taoSmallPrimeUniformLogPowerConstant hC hburgess *
            (8 * iteratedLog x) ^ (50 : ℕ) /
            Real.log (taoZ x) ^ (50 : ℕ) +
          2000001 * (8 * iteratedLog x) ^ (2 : ℕ) /
            ((H x : ℝ) * Real.log (taoZ x) ^ (2 : ℕ)) := by
  have hsmall :=
    eventually_forall_taoBackwardSmallPrimeContribution_sourceLarge_measureReal_le_uniformConstant_of_explicitBurgess
      hC hburgess hscale hP
  have hlarge :=
    eventually_taoBackwardLargePrimeContribution_sourceLarge_measureReal_le_of_explicitBurgess
      hC hburgess hscale hP H m' hH hHpos
  filter_upwards [hsmall, hlarge,
    eventually_taoBackwardExceptionalPrimeLargeEvent_eq_empty, hH, hHpos] with
      x hsmallX hlargeX hexceptional hHx hHxPos
  let E : Set TaoPrimeTuple :=
    {ω | TaoBackwardExceptionalPrimeLargeEvent x (H x) (m' x) ω}
  let S : Set TaoPrimeTuple :=
    {ω | (H x : ℝ) * Real.log (taoZ x) ^ (2 : ℕ) /
        (8 * iteratedLog x) <
      taoBackwardSmallPrimeContribution x (H x) (m' x) ω}
  let L : Set TaoPrimeTuple :=
    {ω | 2000000 * (H x : ℝ) +
          (H x : ℝ) * Real.log (taoZ x) / (8 * iteratedLog x) <
        taoBackwardLargePrimeContribution
          (taoLargePrimeSourceLowerCutoff x)
          (taoLargePrimeSourceUpperCutoff x) (H x) (m' x) ω}
  have hE : E = ∅ := by
    simpa only [E] using hexceptional (H x) (m' x) hHxPos hHx
  have hunion :
      {ω | TaoBackwardSourceAntiSieveLargeEvent x (H x) (m' x) ω} =
        (E ∪ S) ∪ L := by
    ext ω
    simp only [TaoBackwardSourceAntiSieveLargeEvent, E, S, L,
      Set.mem_setOf_eq, Set.mem_union]
    tauto
  rw [hunion]
  calc
    (taoPrimeTupleMeasure (P x) (hP x)).real ((E ∪ S) ∪ L) ≤
        (taoPrimeTupleMeasure (P x) (hP x)).real (E ∪ S) +
          (taoPrimeTupleMeasure (P x) (hP x)).real L :=
      measureReal_union_le _ _
    _ ≤ ((taoPrimeTupleMeasure (P x) (hP x)).real E +
          (taoPrimeTupleMeasure (P x) (hP x)).real S) +
        (taoPrimeTupleMeasure (P x) (hP x)).real L := by
      gcongr
      exact measureReal_union_le _ _
    _ = (taoPrimeTupleMeasure (P x) (hP x)).real S +
        (taoPrimeTupleMeasure (P x) (hP x)).real L := by
      rw [hE]
      simp
    _ ≤ taoSmallPrimeUniformLogPowerConstant hC hburgess *
            (8 * iteratedLog x) ^ (50 : ℕ) /
            Real.log (taoZ x) ^ (50 : ℕ) +
          2000001 * (8 * iteratedLog x) ^ (2 : ℕ) /
            ((H x : ℝ) * Real.log (taoZ x) ^ (2 : ℕ)) := by
      exact add_le_add (by simpa only [S] using hsmallX (H x) (m' x) hHxPos)
        (by simpa only [L] using hlargeX)

noncomputable def taoPrimeTupleBackwardTypicalProbability
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (x H lowerPrime upperPrime m' : ℕ) : ENNReal :=
  taoPrimeTupleMeasure P hP
    {ω | TaoPrimeTupleBackwardTypicalEvent x H lowerPrime upperPrime m' ω}

theorem eventually_measureReal_taoPrimeTupleBackwardTypicalEvent_le_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty)
    (H lowerPrime m' : ℕ → ℕ)
    (hH : ∀ᶠ x : ℕ in atTop, H x ≤ taoTypicalLengthCutoff x)
    (hHpos : ∀ᶠ x : ℕ in atTop, 1 ≤ H x) :
    ∀ᶠ x : ℕ in atTop,
      (taoPrimeTupleMeasure (P x) (hP x)).real
          {ω | TaoPrimeTupleBackwardTypicalEvent x (H x) (lowerPrime x)
            (taoLargePrimeSourceUpperCutoff x) (m' x) ω} ≤
        taoSmallPrimeUniformLogPowerConstant hC hburgess *
            (8 * iteratedLog x) ^ (50 : ℕ) /
            Real.log (taoZ x) ^ (50 : ℕ) +
          2000001 * (8 * iteratedLog x) ^ (2 : ℕ) /
            ((H x : ℝ) * Real.log (taoZ x) ^ (2 : ℕ)) := by
  filter_upwards
    [eventually_measureReal_taoBackwardSourceAntiSieveLargeEvent_le_of_explicitBurgess
      hC hburgess hscale hP H m' hH hHpos,
    eventually_taoPrimeTupleBackwardTypicalEvent_imp_taoBackwardSourceAntiSieveLargeEvent] with
      x htailX hinclusion
  exact (measureReal_mono (fun ω hω =>
    hinclusion (H x) (lowerPrime x) (m' x) ω hω)).trans htailX

theorem eventually_taoPrimeTupleBackwardTypicalProbability_toReal_le_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty)
    (H m' : ℕ → ℕ)
    (hH : ∀ᶠ x : ℕ in atTop, H x ≤ taoTypicalLengthCutoff x)
    (hHpos : ∀ᶠ x : ℕ in atTop, 1 ≤ H x) :
    ∀ᶠ x : ℕ in atTop,
      (taoPrimeTupleBackwardTypicalProbability (P x) (hP x) x (H x)
          (taoZPowerFloor (9 / 10 : ℝ) x)
          (taoLargePrimeSourceUpperCutoff x) (m' x)).toReal ≤
        taoSmallPrimeUniformLogPowerConstant hC hburgess *
            (8 * iteratedLog x) ^ (50 : ℕ) /
            Real.log (taoZ x) ^ (50 : ℕ) +
          2000001 * (8 * iteratedLog x) ^ (2 : ℕ) /
            ((H x : ℝ) * Real.log (taoZ x) ^ (2 : ℕ)) := by
  simpa only [taoPrimeTupleBackwardTypicalProbability, Measure.real]
    using eventually_measureReal_taoPrimeTupleBackwardTypicalEvent_le_of_explicitBurgess
      hC hburgess hscale hP H
        (fun x => taoZPowerFloor (9 / 10 : ℝ) x) m' hH hHpos

/-- Source-facing backward Proposition 6.6 probability bound. -/
theorem exists_eventually_taoPrimeTupleBackwardTypicalProbability_toReal_le_source_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty)
    (H m' : ℕ → ℕ)
    (hH : ∀ᶠ x : ℕ in atTop, H x ≤ taoTypicalLengthCutoff x)
    (hHpos : ∀ᶠ x : ℕ in atTop, 1 ≤ H x) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ x : ℕ in atTop,
      (taoPrimeTupleBackwardTypicalProbability (P x) (hP x) x (H x)
          (taoZPowerFloor (9 / 10 : ℝ) x)
          (taoLargePrimeSourceUpperCutoff x) (m' x)).toReal ≤
        B * (8 * iteratedLog x) ^ (50 : ℕ) /
          ((H x : ℝ) * Real.log (taoZ x) ^ (2 : ℕ)) := by
  let A := taoSmallPrimeUniformLogPowerConstant hC hburgess
  let B : ℝ := A + 2000001
  have hA : 0 < A := by
    exact taoSmallPrimeUniformLogPowerConstant_pos hC hburgess
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨B, hB, ?_⟩
  filter_upwards
    [eventually_taoPrimeTupleBackwardTypicalProbability_toReal_le_of_explicitBurgess
      hC hburgess hscale hP H m' hH hHpos,
    hH, eventually_taoTypicalLengthCutoff_cast_le_log_taoZ_pow_fortyEight,
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
    (taoPrimeTupleBackwardTypicalProbability (P x) (hP x) x (H x)
        (taoZPowerFloor (9 / 10 : ℝ) x)
        (taoLargePrimeSourceUpperCutoff x) (m' x)).toReal ≤
      A * J ^ (50 : ℕ) / L ^ (50 : ℕ) +
        2000001 * J ^ (2 : ℕ) / D := by
      simpa only [A, J, L, D] using hprobX
    _ ≤ A * J ^ (50 : ℕ) / D +
        2000001 * J ^ (50 : ℕ) / D := add_le_add hfirst hsecond
    _ = B * J ^ (50 : ℕ) / D := by
      dsimp only [B]
      ring

/-- Uniform three-branch backward anti-sieve bound. -/
theorem eventually_forall_measureReal_taoBackwardSourceAntiSieveLargeEvent_le_uniformConstant_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty) :
    ∀ᶠ x : ℕ in atTop, ∀ H m' : ℕ,
      1 ≤ H → H ≤ taoTypicalLengthCutoff x →
      (taoPrimeTupleMeasure (P x) (hP x)).real
          {ω | TaoBackwardSourceAntiSieveLargeEvent x H m' ω} ≤
        taoSmallPrimeUniformLogPowerConstant hC hburgess *
            (8 * iteratedLog x) ^ (50 : ℕ) /
            Real.log (taoZ x) ^ (50 : ℕ) +
          2000001 * (8 * iteratedLog x) ^ (2 : ℕ) /
            ((H : ℝ) * Real.log (taoZ x) ^ (2 : ℕ)) := by
  have hsmall :=
    eventually_forall_taoBackwardSmallPrimeContribution_sourceLarge_measureReal_le_uniformConstant_of_explicitBurgess
      hC hburgess hscale hP
  have hlarge :=
    eventually_forall_taoBackwardLargePrimeContribution_sourceLarge_measureReal_le_of_explicitBurgess
      hC hburgess hscale hP
  filter_upwards [hsmall, hlarge,
    eventually_taoBackwardExceptionalPrimeLargeEvent_eq_empty] with
      x hsmallX hlargeX hexceptional H m' hH hHcut
  let E : Set TaoPrimeTuple :=
    {ω | TaoBackwardExceptionalPrimeLargeEvent x H m' ω}
  let S : Set TaoPrimeTuple :=
    {ω | (H : ℝ) * Real.log (taoZ x) ^ (2 : ℕ) /
        (8 * iteratedLog x) < taoBackwardSmallPrimeContribution x H m' ω}
  let L : Set TaoPrimeTuple :=
    {ω | 2000000 * (H : ℝ) +
          (H : ℝ) * Real.log (taoZ x) / (8 * iteratedLog x) <
        taoBackwardLargePrimeContribution
          (taoLargePrimeSourceLowerCutoff x)
          (taoLargePrimeSourceUpperCutoff x) H m' ω}
  have hE : E = ∅ := by
    simpa only [E] using hexceptional H m' hH hHcut
  have hunion :
      {ω | TaoBackwardSourceAntiSieveLargeEvent x H m' ω} = (E ∪ S) ∪ L := by
    ext ω
    simp only [TaoBackwardSourceAntiSieveLargeEvent, E, S, L,
      Set.mem_setOf_eq, Set.mem_union]
    tauto
  rw [hunion]
  calc
    (taoPrimeTupleMeasure (P x) (hP x)).real ((E ∪ S) ∪ L) ≤
        (taoPrimeTupleMeasure (P x) (hP x)).real (E ∪ S) +
          (taoPrimeTupleMeasure (P x) (hP x)).real L :=
      measureReal_union_le _ _
    _ ≤ ((taoPrimeTupleMeasure (P x) (hP x)).real E +
          (taoPrimeTupleMeasure (P x) (hP x)).real S) +
        (taoPrimeTupleMeasure (P x) (hP x)).real L := by
      gcongr
      exact measureReal_union_le _ _
    _ = (taoPrimeTupleMeasure (P x) (hP x)).real S +
        (taoPrimeTupleMeasure (P x) (hP x)).real L := by
      rw [hE]
      simp
    _ ≤ taoSmallPrimeUniformLogPowerConstant hC hburgess *
            (8 * iteratedLog x) ^ (50 : ℕ) /
            Real.log (taoZ x) ^ (50 : ℕ) +
          2000001 * (8 * iteratedLog x) ^ (2 : ℕ) /
            ((H : ℝ) * Real.log (taoZ x) ^ (2 : ℕ)) := by
      exact add_le_add (by simpa only [S] using hsmallX H m' hH)
        (by simpa only [L] using hlargeX H m' hH hHcut)

def taoPrimeTupleBackwardTypicalSupport
    (P : Fin 1001 → ℕ) (x H lowerPrime upperPrime m' : ℕ) :
    Finset TaoPrimeTuple :=
  (taoPrimeTupleSupport P).filter fun ω =>
    TaoPrimeTupleBackwardTypicalEvent x H lowerPrime upperPrime m' ω

theorem mem_taoPrimeTupleBackwardTypicalSupport
    {P : Fin 1001 → ℕ} {x H lowerPrime upperPrime m' : ℕ}
    {ω : TaoPrimeTuple} :
    ω ∈ taoPrimeTupleBackwardTypicalSupport P x H lowerPrime upperPrime m' ↔
      ω ∈ taoPrimeTupleSupport P ∧
        TaoPrimeTupleBackwardTypicalEvent x H lowerPrime upperPrime m' ω := by
  simp [taoPrimeTupleBackwardTypicalSupport]

theorem taoPrimeTupleBackwardTypicalProbability_eq_card_mul_atom
    (P : Fin 1001 → ℕ)
    (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (x H lowerPrime upperPrime m' : ℕ) :
    taoPrimeTupleBackwardTypicalProbability P hP x H lowerPrime upperPrime m' =
      (taoPrimeTupleBackwardTypicalSupport P x H lowerPrime upperPrime m').card *
        (∏ j, ((taoDyadicPrimeBand (P j)).card : ENNReal))⁻¹ := by
  rw [taoPrimeTupleBackwardTypicalProbability,
    taoPrimeTupleMeasure_apply_eq_card_mul_atom]
  congr 2

theorem taoPrimeTupleBackwardTypicalProbability_toReal_eq_card_div
    (P : Fin 1001 → ℕ)
    (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (x H lowerPrime upperPrime m' : ℕ) :
    (taoPrimeTupleBackwardTypicalProbability P hP x H lowerPrime upperPrime m').toReal =
      (taoPrimeTupleBackwardTypicalSupport P x H lowerPrime upperPrime m').card /
        ∏ j, ((taoDyadicPrimeBand (P j)).card : ℝ) := by
  rw [taoPrimeTupleBackwardTypicalProbability_eq_card_mul_atom]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_inv,
    ENNReal.toReal_prod]
  rw [div_eq_mul_inv]

theorem card_taoPrimeTupleBackwardTypicalSupport_le_of_probability
    (P : Fin 1001 → ℕ)
    (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (x H lowerPrime upperPrime m' : ℕ) {B : ℝ}
    (hprob :
      (taoPrimeTupleBackwardTypicalProbability P hP x H lowerPrime upperPrime m').toReal ≤ B) :
    ((taoPrimeTupleBackwardTypicalSupport P x H lowerPrime upperPrime m').card : ℝ) ≤
      B * ∏ j, ((taoDyadicPrimeBand (P j)).card : ℝ) := by
  have hprodPos : 0 < ∏ j, ((taoDyadicPrimeBand (P j)).card : ℝ) := by
    exact Finset.prod_pos fun j _ => by
      exact_mod_cast (Finset.card_pos.mpr (hP j))
  rw [taoPrimeTupleBackwardTypicalProbability_toReal_eq_card_div] at hprob
  exact (div_le_iff₀ hprodPos).mp hprob

/-- Uniform source-facing backward Proposition 6.6, reusing the named bound
from the forward orientation. -/
theorem eventually_forall_taoPrimeTupleBackwardTypicalProbability_toReal_le_source_withLower_uniformConstant_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty)
    (lowerPrime : ℕ → ℕ) :
    ∀ᶠ x : ℕ in atTop, ∀ H m' : ℕ,
      1 ≤ H → H ≤ taoTypicalLengthCutoff x →
      (taoPrimeTupleBackwardTypicalProbability (P x) (hP x) x H
          (lowerPrime x)
          (taoLargePrimeSourceUpperCutoff x) m').toReal ≤
        taoPrimeTupleTypicalUniformSourceConstant hC hburgess *
          (8 * iteratedLog x) ^ (50 : ℕ) /
          ((H : ℝ) * Real.log (taoZ x) ^ (2 : ℕ)) := by
  let A := taoSmallPrimeUniformLogPowerConstant hC hburgess
  let B := taoPrimeTupleTypicalUniformSourceConstant hC hburgess
  have hanti :=
    eventually_forall_measureReal_taoBackwardSourceAntiSieveLargeEvent_le_uniformConstant_of_explicitBurgess
      hC hburgess hscale hP
  filter_upwards [hanti,
    eventually_taoPrimeTupleBackwardTypicalEvent_imp_taoBackwardSourceAntiSieveLargeEvent,
    eventually_taoTypicalLengthCutoff_cast_le_log_taoZ_pow_fortyEight,
    tendsto_iteratedLog_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    (Real.tendsto_log_atTop.comp tendsto_taoZ_atTop).eventually
      (eventually_gt_atTop (0 : ℝ))] with
      x hantiX hinclusion hcutoff hiterX hlogZ H m' hH hHcut
  have hmeasure :
      (taoPrimeTupleBackwardTypicalProbability (P x) (hP x) x H
          (lowerPrime x)
          (taoLargePrimeSourceUpperCutoff x) m').toReal ≤
        A * (8 * iteratedLog x) ^ (50 : ℕ) /
            Real.log (taoZ x) ^ (50 : ℕ) +
          2000001 * (8 * iteratedLog x) ^ (2 : ℕ) /
            ((H : ℝ) * Real.log (taoZ x) ^ (2 : ℕ)) := by
    change (taoPrimeTupleMeasure (P x) (hP x)).real
        {ω | TaoPrimeTupleBackwardTypicalEvent x H
          (lowerPrime x)
          (taoLargePrimeSourceUpperCutoff x) m' ω} ≤ _
    exact (measureReal_mono (fun ω hω =>
      hinclusion H (lowerPrime x) m' ω hω)).trans
        (hantiX H m' hH hHcut)
  let L : ℝ := Real.log (taoZ x)
  let J : ℝ := 8 * iteratedLog x
  let D : ℝ := (H : ℝ) * L ^ (2 : ℕ)
  have hLpos : 0 < L := by simpa only [L] using hlogZ
  have hHrealPos : (0 : ℝ) < H := by exact_mod_cast hH
  have hJone : 1 ≤ J := by dsimp only [J]; nlinarith
  have hDpos : 0 < D := by dsimp only [D]; positivity
  have hHcast : (H : ℝ) ≤ L ^ (48 : ℕ) := by
    have hHreal : (H : ℝ) ≤ taoTypicalLengthCutoff x := by
      exact_mod_cast hHcut
    exact hHreal.trans (by simpa only [L] using hcutoff)
  have hdenom : D ≤ L ^ (50 : ℕ) := by
    dsimp only [D]
    calc
      (H : ℝ) * L ^ (2 : ℕ) ≤
          L ^ (48 : ℕ) * L ^ (2 : ℕ) := by gcongr
      _ = L ^ (50 : ℕ) := by ring
  have hfirst : A * J ^ (50 : ℕ) / L ^ (50 : ℕ) ≤
      A * J ^ (50 : ℕ) / D :=
    div_le_div_of_nonneg_left
      (mul_nonneg
        (taoSmallPrimeUniformLogPowerConstant_pos hC hburgess).le
        (pow_nonneg (by linarith [hJone]) 50)) hDpos hdenom
  have hJpow : J ^ (2 : ℕ) ≤ J ^ (50 : ℕ) :=
    pow_le_pow_right₀ hJone (by norm_num : (2 : ℕ) ≤ 50)
  have hsecond : 2000001 * J ^ (2 : ℕ) / D ≤
      2000001 * J ^ (50 : ℕ) / D := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hJpow (by norm_num)) hDpos.le
  calc
    (taoPrimeTupleBackwardTypicalProbability (P x) (hP x) x H
        (lowerPrime x)
        (taoLargePrimeSourceUpperCutoff x) m').toReal ≤
      A * J ^ (50 : ℕ) / L ^ (50 : ℕ) +
        2000001 * J ^ (2 : ℕ) / D := by
      simpa only [J, L, D] using hmeasure
    _ ≤ A * J ^ (50 : ℕ) / D +
        2000001 * J ^ (50 : ℕ) / D := add_le_add hfirst hsecond
    _ = B * J ^ (50 : ℕ) / D := by
      dsimp only [B, taoPrimeTupleTypicalUniformSourceConstant, A]
      ring
    _ = B * (8 * iteratedLog x) ^ (50 : ℕ) /
        ((H : ℝ) * Real.log (taoZ x) ^ (2 : ℕ)) := rfl

theorem eventually_forall_card_taoPrimeTupleBackwardTypicalSupport_le_source_withLower_uniformConstant_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty)
    (lowerPrime : ℕ → ℕ) :
    ∀ᶠ x : ℕ in atTop, ∀ H m' : ℕ,
      1 ≤ H → H ≤ taoTypicalLengthCutoff x →
      ((taoPrimeTupleBackwardTypicalSupport (P x) x H
          (lowerPrime x)
          (taoLargePrimeSourceUpperCutoff x) m').card : ℝ) ≤
        (taoPrimeTupleTypicalUniformSourceConstant hC hburgess *
          (8 * iteratedLog x) ^ (50 : ℕ) /
          ((H : ℝ) * Real.log (taoZ x) ^ (2 : ℕ))) *
            ∏ j, ((taoDyadicPrimeBand (P x j)).card : ℝ) := by
  have hprob :=
    eventually_forall_taoPrimeTupleBackwardTypicalProbability_toReal_le_source_withLower_uniformConstant_of_explicitBurgess
      hC hburgess hscale hP lowerPrime
  filter_upwards [hprob] with x hx H m' hH hHcut
  exact card_taoPrimeTupleBackwardTypicalSupport_le_of_probability
    (P x) (hP x) x H (lowerPrime x)
      (taoLargePrimeSourceUpperCutoff x) m' (hx H m' hH hHcut)

end

end Tao2026
