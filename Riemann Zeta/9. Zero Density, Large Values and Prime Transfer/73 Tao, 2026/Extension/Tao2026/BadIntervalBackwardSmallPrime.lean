import Tao2026.BadIntervalTypicalUnion

/-!
# Backward typical intervals: finite model and small primes

The second normalized orientation has distinguished product `v = N + H`.
Its other interval elements are `v - l`, for `1 ≤ l < H`.  Congruence
`v ≡ l (mod p)` expresses this divisibility without truncated-natural
subtraction and feeds the same residue-independent character estimates as the
forward `v + l` model.
-/

namespace Tao2026

open Filter MeasureTheory
open scoped Classical BigOperators

noncomputable section

set_option maxRecDepth 12000
set_option maxHeartbeats 800000

/-- The exact right-endpoint typical event for a sampled prime tuple. -/
def TaoPrimeTupleBackwardTypicalEvent
    (x H lowerPrime upperPrime m' : ℕ) (ω : TaoPrimeTuple) : Prop :=
  IsBackwardTypicalScaleNormalizedBadInterval x
    (taoTypicalLengthCutoff x) (taoTypicalSquareThreshold x)
    lowerPrime upperPrime
    (taoPrimeTupleStart m' ω - H) H (ω 0)
    (taoPrimeTupleStart m' ω) (taoPrimeTupleTailProduct ω * m')

/-- Divisibility indicator for a backward shift `v-l`, expressed by a
natural modular congruence. -/
def taoBackwardPrimeDivisibilityIndicator
    (m' l p : ℕ) (ω : TaoPrimeTuple) : ℝ :=
  if taoPrimeTupleStart m' ω ≡ l [MOD p] then 1 else 0

theorem taoBackwardPrimeDivisibilityIndicator_nonneg
    (m' l p : ℕ) (ω : TaoPrimeTuple) :
    0 ≤ taoBackwardPrimeDivisibilityIndicator m' l p ω := by
  unfold taoBackwardPrimeDivisibilityIndicator
  split_ifs <;> norm_num

theorem taoBackwardPrimeDivisibilityIndicator_le_one
    (m' l p : ℕ) (ω : TaoPrimeTuple) :
    taoBackwardPrimeDivisibilityIndicator m' l p ω ≤ 1 := by
  unfold taoBackwardPrimeDivisibilityIndicator
  split_ifs <;> norm_num

/-- One logarithmically weighted backward small-prime term. -/
def taoBackwardSmallAntiSieveTerm
    (m' : ℕ) (lp : ℕ × ℕ) (ω : TaoPrimeTuple) : ℝ :=
  taoBackwardPrimeDivisibilityIndicator m' lp.1 lp.2 ω * Real.log lp.2

/-- Small-prime contribution for the backward orientation. -/
def taoBackwardSmallPrimeContribution
    (x H m' : ℕ) (ω : TaoPrimeTuple) : ℝ :=
  ∑ lp ∈ taoSmallAntiSieveIndices x H,
    taoBackwardSmallAntiSieveTerm m' lp ω

theorem taoBackwardSmallAntiSieveTerm_nonneg
    {x H m' : ℕ} {lp : ℕ × ℕ}
    (hlp : lp ∈ taoSmallAntiSieveIndices x H) (ω : TaoPrimeTuple) :
    0 ≤ taoBackwardSmallAntiSieveTerm m' lp ω := by
  have hpPrime : Nat.Prime lp.2 :=
    (mem_taoSmallAntiSieveIndices.mp hlp).2.2.1
  exact mul_nonneg (taoBackwardPrimeDivisibilityIndicator_nonneg _ _ _ _)
    (Real.log_nonneg (by exact_mod_cast hpPrime.one_le))

theorem taoBackwardSmallPrimeContribution_nonneg
    (x H m' : ℕ) (ω : TaoPrimeTuple) :
    0 ≤ taoBackwardSmallPrimeContribution x H m' ω := by
  exact Finset.sum_nonneg fun lp hlp =>
    taoBackwardSmallAntiSieveTerm_nonneg hlp ω

/-- Joint congruence event in the backward fiftieth-moment expansion. -/
def TaoBackwardSmallPrimeJointDivisibilityEvent
    (m' : ℕ) (t : Fin 50 → ℕ × ℕ) (ω : TaoPrimeTuple) : Prop :=
  ∀ j, taoPrimeTupleStart m' ω ≡ (t j).1 [MOD (t j).2]

theorem taoBackwardSmallPrimeJointDivisibilityEvent_modEq
    {m' : ℕ} {t : Fin 50 → ℕ × ℕ} {ω₁ ω₂ : TaoPrimeTuple}
    (h₁ : TaoBackwardSmallPrimeJointDivisibilityEvent m' t ω₁)
    (h₂ : TaoBackwardSmallPrimeJointDivisibilityEvent m' t ω₂)
    (j : Fin 50) :
    taoPrimeTupleStart m' ω₁ ≡ taoPrimeTupleStart m' ω₂
      [MOD (t j).2] :=
  (h₁ j).trans (h₂ j).symm

theorem taoBackwardSmallPrimeJointDivisibilityEvent_modEq_lcm
    {m' : ℕ} {t : Fin 50 → ℕ × ℕ} {ω₁ ω₂ : TaoPrimeTuple}
    (h₁ : TaoBackwardSmallPrimeJointDivisibilityEvent m' t ω₁)
    (h₂ : TaoBackwardSmallPrimeJointDivisibilityEvent m' t ω₂) :
    taoPrimeTupleStart m' ω₁ ≡ taoPrimeTupleStart m' ω₂
      [MOD taoSmallPrimeTupleModulus t] := by
  by_cases hle : taoPrimeTupleStart m' ω₁ ≤ taoPrimeTupleStart m' ω₂
  · apply (Nat.modEq_iff_dvd' hle).2
    apply Finset.lcm_dvd
    intro j _hj
    exact (Nat.modEq_iff_dvd' hle).1
      (taoBackwardSmallPrimeJointDivisibilityEvent_modEq h₁ h₂ j)
  · have hle' : taoPrimeTupleStart m' ω₂ ≤ taoPrimeTupleStart m' ω₁ :=
      le_of_not_ge hle
    apply Nat.ModEq.symm
    apply (Nat.modEq_iff_dvd' hle').2
    apply Finset.lcm_dvd
    intro j _hj
    exact (Nat.modEq_iff_dvd' hle').1
      (taoBackwardSmallPrimeJointDivisibilityEvent_modEq h₂ h₁ j)

theorem TaoBackwardSmallPrimeJointDivisibilityEvent.of_modEq_lcm
    {m' : ℕ} {t : Fin 50 → ℕ × ℕ} {ω₀ ω : TaoPrimeTuple}
    (h₀ : TaoBackwardSmallPrimeJointDivisibilityEvent m' t ω₀)
    (hω : taoPrimeTupleStart m' ω ≡ taoPrimeTupleStart m' ω₀
      [MOD taoSmallPrimeTupleModulus t]) :
    TaoBackwardSmallPrimeJointDivisibilityEvent m' t ω := by
  intro j
  have hpMod : taoPrimeTupleStart m' ω ≡ taoPrimeTupleStart m' ω₀
      [MOD (t j).2] :=
    hω.of_dvd (Finset.dvd_lcm (f := fun i : Fin 50 => (t i).2)
      (Finset.mem_univ j))
  exact hpMod.trans (h₀ j)

theorem TaoBackwardSmallPrimeJointDivisibilityEvent.coprime_modulus
    {x H m' : ℕ} {t : Fin 50 → ℕ × ℕ} {ω : TaoPrimeTuple}
    (ht : t ∈ Fintype.piFinset
      (fun _ : Fin 50 => taoSmallAntiSieveIndices x H))
    (hω : TaoBackwardSmallPrimeJointDivisibilityEvent m' t ω) :
    Nat.Coprime (taoSmallPrimeTupleModulus t)
      (taoPrimeTupleStart m' ω) := by
  apply Nat.Coprime.of_dvd_left
    (Finset.lcm_dvd_prod (Finset.univ : Finset (Fin 50))
      (fun j => (t j).2))
  rw [Nat.coprime_prod_left_iff]
  intro j _hj
  have htj := Fintype.mem_piFinset.mp ht j
  have hpPrime : Nat.Prime (t j).2 :=
    (mem_taoSmallAntiSieveIndices.mp htj).2.2.1
  have hpNotL : ¬(t j).2 ∣ (t j).1 :=
    (mem_taoSmallAntiSieveIndices.mp htj).2.2.2.2
  apply hpPrime.coprime_iff_not_dvd.mpr
  intro hpStart
  have hlMod : (t j).1 ≡ 0 [MOD (t j).2] :=
    (hω j).symm.trans hpStart.modEq_zero_nat
  exact hpNotL (Nat.modEq_zero_iff_dvd.mp hlMod)

/-- A backward joint event is empty or one primitive residue fiber. -/
theorem taoBackwardSmallPrimeJointDivisibilityEvent_empty_or_primitiveResidueClass
    {x H : ℕ} (m' : ℕ) {t : Fin 50 → ℕ × ℕ}
    (ht : t ∈ Fintype.piFinset
      (fun _ : Fin 50 => taoSmallAntiSieveIndices x H)) :
    {ω : TaoPrimeTuple |
      TaoBackwardSmallPrimeJointDivisibilityEvent m' t ω} = ∅ ∨
      ∃ a : ℕ,
        Nat.Coprime a (taoSmallPrimeTupleModulus t) ∧
          {ω : TaoPrimeTuple |
            TaoBackwardSmallPrimeJointDivisibilityEvent m' t ω} =
            {ω | taoPrimeTupleStart m' ω ≡ a
              [MOD taoSmallPrimeTupleModulus t]} := by
  by_cases hE : ∃ ω : TaoPrimeTuple,
      TaoBackwardSmallPrimeJointDivisibilityEvent m' t ω
  · right
    obtain ⟨ω₀, hω₀⟩ := hE
    refine ⟨taoPrimeTupleStart m' ω₀, ?_, ?_⟩
    · exact (hω₀.coprime_modulus ht).symm
    · ext ω
      constructor
      · intro hω
        exact taoBackwardSmallPrimeJointDivisibilityEvent_modEq_lcm hω hω₀
      · intro hω
        exact hω₀.of_modEq_lcm hω
  · left
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact fun hω => hE ⟨ω, hω⟩

theorem prod_taoBackwardSmallAntiSieveTerm_eq
    (m' : ℕ) (t : Fin 50 → ℕ × ℕ) (ω : TaoPrimeTuple) :
    (∏ j, taoBackwardSmallAntiSieveTerm m' (t j) ω) =
      (∏ j, Real.log (t j).2) *
        if TaoBackwardSmallPrimeJointDivisibilityEvent m' t ω then 1 else 0 := by
  rw [show (∏ j, taoBackwardSmallAntiSieveTerm m' (t j) ω) =
      (∏ j, taoBackwardPrimeDivisibilityIndicator
        m' (t j).1 (t j).2 ω) * ∏ j, Real.log (t j).2 by
    simp only [taoBackwardSmallAntiSieveTerm, Finset.prod_mul_distrib]]
  by_cases h : TaoBackwardSmallPrimeJointDivisibilityEvent m' t ω
  · have hj : ∀ j, taoPrimeTupleStart m' ω ≡ (t j).1 [MOD (t j).2] := h
    simp [taoBackwardPrimeDivisibilityIndicator, hj, h]
  · have hj : ∃ j, ¬taoPrimeTupleStart m' ω ≡ (t j).1 [MOD (t j).2] := by
      simpa [TaoBackwardSmallPrimeJointDivisibilityEvent] using h
    obtain ⟨j, hj⟩ := hj
    have hzero :
        (∏ i, taoBackwardPrimeDivisibilityIndicator
          m' (t i).1 (t i).2 ω) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [taoBackwardPrimeDivisibilityIndicator, hj]
    rw [hzero]
    simp [h]

theorem taoBackwardSmallPrimeContribution_pow_fifty
    (x H m' : ℕ) (ω : TaoPrimeTuple) :
    (taoBackwardSmallPrimeContribution x H m' ω) ^ (50 : ℕ) =
      ∑ t ∈ Fintype.piFinset
          (fun _ : Fin 50 => taoSmallAntiSieveIndices x H),
        (∏ j, Real.log (t j).2) *
          if TaoBackwardSmallPrimeJointDivisibilityEvent m' t ω
            then 1 else 0 := by
  unfold taoBackwardSmallPrimeContribution
  rw [Finset.sum_pow']
  apply Finset.sum_congr rfl
  intro t _ht
  exact prod_taoBackwardSmallAntiSieveTerm_eq m' t ω

/-- Backward small-prime fiftieth moment. -/
def taoBackwardSmallPrimeFiftiethMoment
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (x H m' : ℕ) : ℝ :=
  ∫ ω, (taoBackwardSmallPrimeContribution x H m' ω) ^ (50 : ℕ)
    ∂taoPrimeTupleMeasure P hP

theorem taoBackwardSmallPrimeFiftiethMoment_eq_sum_jointProbabilities
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (x H m' : ℕ) :
    taoBackwardSmallPrimeFiftiethMoment P hP x H m' =
      ∑ t ∈ Fintype.piFinset
          (fun _ : Fin 50 => taoSmallAntiSieveIndices x H),
        (∏ j, Real.log (t j).2) *
          (taoPrimeTupleMeasure P hP).real
            {ω | TaoBackwardSmallPrimeJointDivisibilityEvent m' t ω} := by
  let S := Fintype.piFinset
    (fun _ : Fin 50 => taoSmallAntiSieveIndices x H)
  have hmeas : ∀ t : Fin 50 → ℕ × ℕ,
      MeasurableSet {ω : TaoPrimeTuple |
        TaoBackwardSmallPrimeJointDivisibilityEvent m' t ω} := by
    intro t
    exact (Set.to_countable _).measurableSet
  have hterm : ∀ t : Fin 50 → ℕ × ℕ,
      Integrable
        (fun ω => (∏ j, Real.log (t j).2) *
          if TaoBackwardSmallPrimeJointDivisibilityEvent m' t ω
            then 1 else 0)
        (taoPrimeTupleMeasure P hP) := by
    intro t
    have hi : Integrable
        ({ω : TaoPrimeTuple |
          TaoBackwardSmallPrimeJointDivisibilityEvent m' t ω}.indicator
            (fun _ => (1 : ℝ))) (taoPrimeTupleMeasure P hP) :=
      (integrable_const (1 : ℝ)).indicator (hmeas t)
    simpa only [Set.indicator, Set.mem_setOf_eq] using
      hi.const_mul (∏ j, Real.log (t j).2)
  unfold taoBackwardSmallPrimeFiftiethMoment
  calc
    (∫ ω, (taoBackwardSmallPrimeContribution x H m' ω) ^ (50 : ℕ)
        ∂taoPrimeTupleMeasure P hP) =
      ∫ ω, ∑ t ∈ S,
        (∏ j, Real.log (t j).2) *
          if TaoBackwardSmallPrimeJointDivisibilityEvent m' t ω
            then 1 else 0 ∂taoPrimeTupleMeasure P hP := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => by
        simpa only [S] using
          taoBackwardSmallPrimeContribution_pow_fifty x H m' ω
    _ = ∑ t ∈ S, ∫ ω,
        (∏ j, Real.log (t j).2) *
          if TaoBackwardSmallPrimeJointDivisibilityEvent m' t ω
            then 1 else 0 ∂taoPrimeTupleMeasure P hP := by
      exact integral_finsetSum S fun t _ht => hterm t
    _ = ∑ t ∈ S, (∏ j, Real.log (t j).2) *
        (taoPrimeTupleMeasure P hP).real
          {ω | TaoBackwardSmallPrimeJointDivisibilityEvent m' t ω} := by
      apply Finset.sum_congr rfl
      intro t _ht
      rw [show (fun ω : TaoPrimeTuple =>
          (∏ j, Real.log (t j).2) *
            if TaoBackwardSmallPrimeJointDivisibilityEvent m' t ω
              then (1 : ℝ) else 0) =
          fun ω => (∏ j, Real.log (t j).2) *
            {ω : TaoPrimeTuple |
              TaoBackwardSmallPrimeJointDivisibilityEvent m' t ω}.indicator
                (fun _ => (1 : ℝ)) ω by
        funext ω
        simp only [Set.indicator, Set.mem_setOf_eq]]
      rw [integral_const_mul]
      change (∏ j, Real.log (t j).2) *
          (∫ ω : TaoPrimeTuple,
            {ω : TaoPrimeTuple |
              TaoBackwardSmallPrimeJointDivisibilityEvent m' t ω}.indicator 1 ω
              ∂taoPrimeTupleMeasure P hP) = _
      rw [integral_indicator_one (hmeas t)]
    _ = _ := by rfl

theorem taoBackwardSmallPrimeJointDivisibilityProbability_le_modulusCharacterMoments
    {x H : ℕ} (P : Fin 1001 → ℕ)
    (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (m' : ℕ) {t : Fin 50 → ℕ × ℕ}
    (ht : t ∈ Fintype.piFinset
      (fun _ : Fin 50 => taoSmallAntiSieveIndices x H)) :
    (taoPrimeTupleMeasure P hP).real
        {ω | TaoBackwardSmallPrimeJointDivisibilityEvent m' t ω} ≤
      ((2 ^ (50 : ℕ) : ℝ) / taoSmallPrimeTupleModulus t) *
        ∑ χ : DirichletCharacter ℂ (taoSmallPrimeTupleModulus t),
          ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
            ‖taoDyadicPrimeCharacterAverage χ (P j)‖ ^ (1000 : ℕ) := by
  rcases
      taoBackwardSmallPrimeJointDivisibilityEvent_empty_or_primitiveResidueClass
        m' ht with hEmpty | ⟨a, ha, hFiber⟩
  · rw [hEmpty]
    simp only [measureReal_empty]
    positivity
  · rw [hFiber]
    calc
      (taoPrimeTupleMeasure P hP).real
          {ω | taoPrimeTupleStart m' ω ≡ a
            [MOD taoSmallPrimeTupleModulus t]} ≤
        ‖(1 / ((taoSmallPrimeTupleModulus t).totient : ℂ))‖ *
          ∑ χ : DirichletCharacter ℂ (taoSmallPrimeTupleModulus t),
            ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
              ‖taoDyadicPrimeCharacterAverage χ (P j)‖ ^ (1000 : ℕ) :=
        primitiveResidueFiber_probability_le_primeCharacterMoments
          (taoSmallPrimeTupleModulus_pos_of_mem ht) ha P hP m'
      _ ≤ ((2 ^ (50 : ℕ) : ℝ) / taoSmallPrimeTupleModulus t) *
          ∑ χ : DirichletCharacter ℂ (taoSmallPrimeTupleModulus t),
            ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
              ‖taoDyadicPrimeCharacterAverage χ (P j)‖ ^ (1000 : ℕ) := by
        apply mul_le_mul_of_nonneg_right
          (norm_one_div_taoSmallPrimeTupleTotient_le ht)
        exact Finset.sum_nonneg fun _ _ =>
          Finset.sum_nonneg fun _ _ => pow_nonneg (norm_nonneg _) _

theorem taoBackwardSmallPrimeFiftiethMoment_le_sum_coordinateCharacterMoments
    (P : Fin 1001 → ℕ)
    (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (x H m' : ℕ) :
    taoBackwardSmallPrimeFiftiethMoment P hP x H m' ≤
      ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
        taoSmallPrimeCharacterMomentAtCoordinate P x H j := by
  rw [taoBackwardSmallPrimeFiftiethMoment_eq_sum_jointProbabilities]
  calc
    (∑ t ∈ Fintype.piFinset
        (fun _ : Fin 50 => taoSmallAntiSieveIndices x H),
      (∏ j, Real.log (t j).2) *
        (taoPrimeTupleMeasure P hP).real
          {ω | TaoBackwardSmallPrimeJointDivisibilityEvent m' t ω}) ≤
      ∑ t ∈ Fintype.piFinset
          (fun _ : Fin 50 => taoSmallAntiSieveIndices x H),
        (∏ j, Real.log (t j).2) *
          (((2 ^ (50 : ℕ) : ℝ) / taoSmallPrimeTupleModulus t) *
            ∑ χ : DirichletCharacter ℂ (taoSmallPrimeTupleModulus t),
              ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
                ‖taoDyadicPrimeCharacterAverage χ (P j)‖ ^
                  (1000 : ℕ)) := by
      apply Finset.sum_le_sum
      intro t ht
      apply mul_le_mul_of_nonneg_left
        (taoBackwardSmallPrimeJointDivisibilityProbability_le_modulusCharacterMoments
          P hP m' ht)
      apply Finset.prod_nonneg
      intro j _hj
      have htj := Fintype.mem_piFinset.mp ht j
      have hp : Nat.Prime (t j).2 :=
        (mem_taoSmallAntiSieveIndices.mp htj).2.2.1
      exact Real.log_nonneg (by exact_mod_cast hp.one_le)
    _ = ∑ j ∈ Finset.univ.erase (0 : Fin 1001),
        taoSmallPrimeCharacterMomentAtCoordinate P x H j := by
      simp only [taoSmallPrimeCharacterMomentAtCoordinate, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Finset.sum_comm]

theorem exists_taoBackwardSmallPrimeFiftiethMoment_le_coordinateCharacterMoment
    (P : Fin 1001 → ℕ)
    (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (x H m' : ℕ) :
    ∃ j ∈ Finset.univ.erase (0 : Fin 1001),
      taoBackwardSmallPrimeFiftiethMoment P hP x H m' ≤
        1000 * taoSmallPrimeCharacterMomentAtCoordinate P x H j := by
  let s : Finset (Fin 1001) := Finset.univ.erase 0
  let A : Fin 1001 → ℝ := taoSmallPrimeCharacterMomentAtCoordinate P x H
  have hs : s.Nonempty := by
    refine ⟨(1 : Fin 1001), ?_⟩
    simp [s]
  let values : Finset ℝ := s.image A
  have hvalues : values.Nonempty := hs.image A
  let M : ℝ := values.max' hvalues
  have hMmem : M ∈ values := Finset.max'_mem values hvalues
  rcases Finset.mem_image.mp hMmem with ⟨j, hj, hAj⟩
  refine ⟨j, hj, ?_⟩
  have hle : ∀ k ∈ s, A k ≤ M := by
    intro k hk
    exact Finset.le_max' values (A k)
      (Finset.mem_image.mpr ⟨k, hk, rfl⟩)
  have hsum : (∑ k ∈ s, A k) ≤ s.card • M :=
    Finset.sum_le_card_nsmul s A M hle
  have hcard : s.card = 1000 := by simp [s]
  calc
    taoBackwardSmallPrimeFiftiethMoment P hP x H m' ≤ ∑ k ∈ s, A k :=
      taoBackwardSmallPrimeFiftiethMoment_le_sum_coordinateCharacterMoments
        P hP x H m'
    _ ≤ s.card • M := hsum
    _ = 1000 * taoSmallPrimeCharacterMomentAtCoordinate P x H j := by
      simp only [hcard, nsmul_eq_mul, Nat.cast_ofNat]
      change 1000 * M = 1000 * A j
      rw [hAj]

theorem exists_taoBackwardSmallPrimeFiftiethMoment_le_conductorBound
    (P : Fin 1001 → ℕ)
    (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (x H m' : ℕ)
    (hcutoff : ∀ j ∈ Finset.univ.erase (0 : Fin 1001),
      taoSmallAntiSievePrimeCutoff x < P j) :
    ∃ j ∈ Finset.univ.erase (0 : Fin 1001),
      taoBackwardSmallPrimeFiftiethMoment P hP x H m' ≤
        1000 * taoSmallPrimeConductorBoundAtCoordinate P x H j := by
  rcases exists_taoBackwardSmallPrimeFiftiethMoment_le_coordinateCharacterMoment
      P hP x H m' with ⟨j, hj, hMoment⟩
  refine ⟨j, hj, hMoment.trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (taoSmallPrimeCharacterMomentAtCoordinate_le_conductorBound
      P x H j (hcutoff j hj) (hP j)) (by norm_num)

theorem exists_taoBackwardSmallPrimeFiftiethMoment_le_exceptional_add_elementary
    (P : Fin 1001 → ℕ)
    (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (x H m' : ℕ)
    (hcutoffSep : ∀ j ∈ Finset.univ.erase (0 : Fin 1001),
      taoSmallAntiSievePrimeCutoff x < P j)
    (hcutoffPos : 0 < taoSmallAntiSievePrimeCutoff x) :
    ∃ j ∈ Finset.univ.erase (0 : Fin 1001),
      taoBackwardSmallPrimeFiftiethMoment P hP x H m' ≤
        1000 * (taoSmallPrimePrincipalMertensMajorant x H +
          taoSmallPrimeExceptionalConductorSum P x H j +
            taoSmallPrimeTotientErrorMajorant P x H j) := by
  rcases exists_taoBackwardSmallPrimeFiftiethMoment_le_conductorBound
      P hP x H m' hcutoffSep with ⟨j, hj, hmoment⟩
  refine ⟨j, hj, hmoment.trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (taoSmallPrimeConductorBoundAtCoordinate_le_exceptional_add_elementary
      P x H j hcutoffPos) (by norm_num)

/-- The named Burgess constant controls the backward small-prime moment
simultaneously in the length and remainder. -/
theorem eventually_forall_taoBackwardSmallPrimeFiftiethMoment_le_principalMajorant_uniformConstant_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty) :
    ∀ᶠ x : ℕ in atTop, ∀ H m' : ℕ,
      taoBackwardSmallPrimeFiftiethMoment (P x) (hP x) x H m' ≤
        1000 * (2 + taoUniformExceptionalSecondMomentConstant hC hburgess) *
          taoSmallPrimePrincipalMertensMajorant x H := by
  have hscaleNat : ∀ᶠ x : ℕ in atTop, ∀ j,
      taoZPowerFloor (9 / 10 : ℝ) x ≤ P x j := by
    filter_upwards
      [eventually_taoPrimeTupleSourceScale_lower_nine_tenths hscale] with
        x hx j
    have hfloor : (taoZPowerFloor (9 / 10 : ℝ) x : ℝ) ≤
        (taoZ x) ^ (9 / 10 : ℝ) :=
      Nat.floor_le (Real.rpow_nonneg (taoZ_pos x).le _)
    exact_mod_cast hfloor.trans (hx j)
  let K := taoUniformExceptionalSecondMomentConstant hC hburgess
  have hK : 0 < K := taoUniformExceptionalSecondMomentConstant_pos hC hburgess
  have huniform :=
    eventually_conductorExceptional_secondMoment_le_uniformConstant hC hburgess
  rw [eventually_atTop] at huniform
  obtain ⟨Z₀, hZ₀⟩ := huniform
  have hlower : ∀ᶠ x : ℕ in atTop,
      Z₀ ≤ taoZPowerFloor (9 / 10 : ℝ) x :=
    (tendsto_taoZPowerFloor_atTop
      (by norm_num : (0 : ℝ) < 9 / 10)).eventually (eventually_ge_atTop Z₀)
  have hseparation :=
    eventually_taoSmallAntiSievePrimeCutoff_lt_of_lowerScale P hscaleNat
  have hcutoffPos : ∀ᶠ x : ℕ in atTop,
      0 < taoSmallAntiSievePrimeCutoff x :=
    (tendsto_taoZPowerFloor_atTop
      (by norm_num : (0 : ℝ) < 1 / 100)).eventually (eventually_gt_atTop 0)
  have hcutoffOne : ∀ᶠ x : ℕ in atTop,
      1 ≤ taoSmallAntiSievePrimeCutoff x :=
    (tendsto_taoZPowerFloor_atTop
      (by norm_num : (0 : ℝ) < 1 / 100)).eventually (eventually_ge_atTop 1)
  filter_upwards [
    eventually_taoSmallAntiSievePrimeCutoff_pow_fifty_le_burgessRange,
    eventually_taoSmallAntiSievePrimeCutoff_pow_fifty_le_lowerScale,
    hscaleNat, hlower, hseparation, hcutoffPos, hcutoffOne] with
      x hrange hcutPower hxscale hxlower hsep hcutPos hcutOne H m'
  obtain ⟨j, hj, hmoment⟩ :=
    exists_taoBackwardSmallPrimeFiftiethMoment_le_exceptional_add_elementary
      (P x) (hP x) x H m' (fun j hj => hsep j) hcutPos
  have hadmissible : IsAdmissibleTaoExceptionalConductorSet
      (taoSmallPrimeExceptionalConductors x H) (P x j) :=
    isAdmissible_taoSmallPrimeExceptionalConductors
      (hrange (P x j) (hxscale j))
  have hexceptionalMoment :
      (∑ d ∈ taoSmallPrimeExceptionalConductors x H,
        ∑ χ ∈ taoExceptionalPrimitiveCharacters d (P x j),
          ‖taoNormalizedPrimeCharacterSum χ (P x j)‖ ^ 2) ≤ K :=
    hZ₀ (P x j) (hxlower.trans (hxscale j)) _ hadmissible
  have hexceptional :
      taoSmallPrimeExceptionalConductorSum (P x) x H j ≤
        K * taoSmallPrimePrincipalMertensMajorant x H := by
    calc
      taoSmallPrimeExceptionalConductorSum (P x) x H j ≤
          (2 : ℝ) ^ (50 : ℕ) * K *
            ((H : ℝ) ^ (50 : ℕ) *
              ((50 : ℝ) ^ (50 : ℕ) * 50 *
                (Real.log 4 *
                    (2 + Real.log (taoSmallAntiSievePrimeCutoff x)) +
                  Real.log (taoSmallAntiSievePrimeCutoff x)) ^ (50 : ℕ))) :=
        taoSmallPrimeExceptionalConductorSum_le_log_pow_fifty_of_unionMoment
          (P x) x H j hK.le hcutPos hexceptionalMoment
      _ = K * taoSmallPrimePrincipalMertensMajorant x H := by
        rw [taoSmallPrimePrincipalMertensMajorant]
        ac_rfl
  have herror :=
    taoSmallPrimeTotientErrorMajorant_le_principalMertensMajorant
      (P x) x H j hcutOne (hcutPower.trans (hxscale j))
  calc
    taoBackwardSmallPrimeFiftiethMoment (P x) (hP x) x H m' ≤
        1000 * (taoSmallPrimePrincipalMertensMajorant x H +
          taoSmallPrimeExceptionalConductorSum (P x) x H j +
            taoSmallPrimeTotientErrorMajorant (P x) x H j) := hmoment
    _ ≤ 1000 * (taoSmallPrimePrincipalMertensMajorant x H +
          K * taoSmallPrimePrincipalMertensMajorant x H +
            taoSmallPrimePrincipalMertensMajorant x H) := by gcongr
    _ = 1000 * (2 + K) * taoSmallPrimePrincipalMertensMajorant x H := by ring

theorem eventually_forall_taoBackwardSmallPrimeFiftiethMoment_le_logPower_uniformConstant_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty) :
    ∀ᶠ x : ℕ in atTop, ∀ H m' : ℕ,
      taoBackwardSmallPrimeFiftiethMoment (P x) (hP x) x H m' ≤
        taoSmallPrimeUniformLogPowerConstant hC hburgess *
          (H : ℝ) ^ (50 : ℕ) *
          Real.log (taoZ x) ^ (50 : ℕ) := by
  have hmoment :=
    eventually_forall_taoBackwardSmallPrimeFiftiethMoment_le_principalMajorant_uniformConstant_of_explicitBurgess
      hC hburgess hscale hP
  filter_upwards [hmoment,
    eventually_forall_taoSmallPrimePrincipalMertensMajorant_le_logPower] with
      x hmomentX hmajorantX H m'
  calc
    taoBackwardSmallPrimeFiftiethMoment (P x) (hP x) x H m' ≤
        1000 * (2 + taoUniformExceptionalSecondMomentConstant hC hburgess) *
          taoSmallPrimePrincipalMertensMajorant x H := hmomentX H m'
    _ ≤ 1000 * (2 + taoUniformExceptionalSecondMomentConstant hC hburgess) *
        (taoSmallPrimePrincipalLogPowerConstant *
          (H : ℝ) ^ (50 : ℕ) * Real.log (taoZ x) ^ (50 : ℕ)) := by
      exact mul_le_mul_of_nonneg_left (hmajorantX H)
        (mul_nonneg (by norm_num)
          (by linarith [
            taoUniformExceptionalSecondMomentConstant_pos hC hburgess]))
    _ = taoSmallPrimeUniformLogPowerConstant hC hburgess *
        (H : ℝ) ^ (50 : ℕ) *
        Real.log (taoZ x) ^ (50 : ℕ) := by
      unfold taoSmallPrimeUniformLogPowerConstant
      ring

theorem integrable_taoBackwardSmallPrimeContribution_pow_fifty
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (x H m' : ℕ) :
    Integrable (fun ω : TaoPrimeTuple =>
      (taoBackwardSmallPrimeContribution x H m' ω) ^ (50 : ℕ))
      (taoPrimeTupleMeasure P hP) := by
  rw [show (fun ω : TaoPrimeTuple =>
      (taoBackwardSmallPrimeContribution x H m' ω) ^ (50 : ℕ)) =
      fun ω => ∑ t ∈ Fintype.piFinset
          (fun _ : Fin 50 => taoSmallAntiSieveIndices x H),
        (∏ j, Real.log (t j).2) *
          if TaoBackwardSmallPrimeJointDivisibilityEvent m' t ω
            then 1 else 0 by
    funext ω
    exact taoBackwardSmallPrimeContribution_pow_fifty x H m' ω]
  apply integrable_finsetSum
  intro t _ht
  have hm : MeasurableSet {ω : TaoPrimeTuple |
      TaoBackwardSmallPrimeJointDivisibilityEvent m' t ω} :=
    (Set.to_countable _).measurableSet
  have hi : Integrable
      ({ω : TaoPrimeTuple |
        TaoBackwardSmallPrimeJointDivisibilityEvent m' t ω}.indicator
          (fun _ => (1 : ℝ))) (taoPrimeTupleMeasure P hP) :=
    (integrable_const (1 : ℝ)).indicator hm
  simpa only [Set.indicator, Set.mem_setOf_eq] using
    hi.const_mul (∏ j, Real.log (t j).2)

theorem taoBackwardSmallPrimeContribution_large_measureReal_mul_pow_fifty_le
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (x H m' : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    T ^ (50 : ℕ) *
        (taoPrimeTupleMeasure P hP).real
          {ω | T < taoBackwardSmallPrimeContribution x H m' ω} ≤
      taoBackwardSmallPrimeFiftiethMoment P hP x H m' := by
  let μ := taoPrimeTupleMeasure P hP
  let X : TaoPrimeTuple → ℝ := fun ω =>
    taoBackwardSmallPrimeContribution x H m' ω
  have hnonneg : ∀ ω, 0 ≤ X ω := fun ω =>
    taoBackwardSmallPrimeContribution_nonneg x H m' ω
  have hsubset : {ω | T < X ω} ⊆
      {ω | T ^ (50 : ℕ) ≤ (X ω) ^ (50 : ℕ)} := by
    intro ω hω
    exact pow_le_pow_left₀ hT (le_of_lt hω) 50
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := fun ω => (X ω) ^ (50 : ℕ))
      (Filter.Eventually.of_forall fun ω => pow_nonneg (hnonneg ω) 50)
      (by
        simpa only [μ, X] using
          integrable_taoBackwardSmallPrimeContribution_pow_fifty
            P hP x H m')
      (T ^ (50 : ℕ))
  calc
    T ^ (50 : ℕ) * μ.real {ω | T < X ω} ≤
        T ^ (50 : ℕ) * μ.real
          {ω | T ^ (50 : ℕ) ≤ (X ω) ^ (50 : ℕ)} := by
      exact mul_le_mul_of_nonneg_left (measureReal_mono hsubset)
        (pow_nonneg hT 50)
    _ ≤ ∫ ω, (X ω) ^ (50 : ℕ) ∂μ := hmarkov
    _ = taoBackwardSmallPrimeFiftiethMoment P hP x H m' := by rfl

theorem eventually_forall_taoBackwardSmallPrimeContribution_sourceLarge_measureReal_le_uniformConstant_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty) :
    ∀ᶠ x : ℕ in atTop, ∀ H m' : ℕ, 1 ≤ H →
      (taoPrimeTupleMeasure (P x) (hP x)).real
          {ω | (H : ℝ) * Real.log (taoZ x) ^ (2 : ℕ) /
                (8 * iteratedLog x) <
            taoBackwardSmallPrimeContribution x H m' ω} ≤
        taoSmallPrimeUniformLogPowerConstant hC hburgess *
          (8 * iteratedLog x) ^ (50 : ℕ) /
          Real.log (taoZ x) ^ (50 : ℕ) := by
  let A := taoSmallPrimeUniformLogPowerConstant hC hburgess
  have hmoment :=
    eventually_forall_taoBackwardSmallPrimeFiftiethMoment_le_logPower_uniformConstant_of_explicitBurgess
      hC hburgess hscale hP
  filter_upwards [hmoment,
    tendsto_taoZ_atTop.eventually (eventually_gt_atTop (1 : ℝ)),
    tendsto_iteratedLog_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with
      x hmomentX hz hiter H m' hH
  let L : ℝ := Real.log (taoZ x)
  let I : ℝ := iteratedLog x
  let T : ℝ := (H : ℝ) * L ^ (2 : ℕ) / (8 * I)
  let Q : ℝ := (taoPrimeTupleMeasure (P x) (hP x)).real
    {ω | T < taoBackwardSmallPrimeContribution x H m' ω}
  have hLpos : 0 < L := by dsimp only [L]; exact Real.log_pos hz
  have hHrealPos : (0 : ℝ) < H := by exact_mod_cast hH
  have hIpos : 0 < I := by simpa only [I] using hiter
  have hTpos : 0 < T := by dsimp only [T]; positivity
  have hmarkov :=
    taoBackwardSmallPrimeContribution_large_measureReal_mul_pow_fifty_le
      (P x) (hP x) x H m' (T := T) hTpos.le
  have htail : T ^ (50 : ℕ) * Q ≤
      A * (H : ℝ) ^ (50 : ℕ) * L ^ (50 : ℕ) := by
    exact hmarkov.trans (by simpa only [Q, T, L] using hmomentX H m')
  have hQ : Q ≤
      (A * (H : ℝ) ^ (50 : ℕ) * L ^ (50 : ℕ)) /
        T ^ (50 : ℕ) := by
    rw [le_div_iff₀ (pow_pos hTpos 50)]
    simpa only [mul_comm] using htail
  change Q ≤ A * (8 * I) ^ (50 : ℕ) / L ^ (50 : ℕ)
  calc
    Q ≤ (A * (H : ℝ) ^ (50 : ℕ) * L ^ (50 : ℕ)) /
        T ^ (50 : ℕ) := hQ
    _ = A * (8 * I) ^ (50 : ℕ) / L ^ (50 : ℕ) := by
      dsimp only [T]
      field_simp [hHrealPos.ne', hLpos.ne', hIpos.ne']


end

end Tao2026
