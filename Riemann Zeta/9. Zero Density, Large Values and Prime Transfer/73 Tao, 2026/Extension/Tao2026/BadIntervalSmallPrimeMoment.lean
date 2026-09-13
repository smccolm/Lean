import Tao2026.BadIntervalAntiSieve

/-!
# The fiftieth-moment expansion for Proposition 6.6

This module sets up the source's small-prime branch exactly.  The prime
cutoff is `floor (z^(1/100))`, the shifts are `1 ≤ l < H`, primes dividing
the shift are removed, and the fixed moment is 50.  The final theorem expands
the expectation into the finite sum of joint divisibility probabilities to
which the character estimates are applied.
-/

namespace Tao2026

open MeasureTheory
open scoped Classical

noncomputable section

/-- Source cutoff `floor (z^(1/100))` for the high-moment branch. -/
def taoSmallAntiSievePrimeCutoff (x : ℕ) : ℕ :=
  taoZPowerFloor (1 / 100 : ℝ) x

/-- Primes at most `floor (z^(1/100))`. -/
def taoSmallAntiSievePrimeRange (x : ℕ) : Finset ℕ :=
  (Finset.range (taoSmallAntiSievePrimeCutoff x + 1)).filter Nat.Prime

theorem mem_taoSmallAntiSievePrimeRange {x p : ℕ} :
    p ∈ taoSmallAntiSievePrimeRange x ↔
      Nat.Prime p ∧ p ≤ taoSmallAntiSievePrimeCutoff x := by
  simp [taoSmallAntiSievePrimeRange, and_comm]

/-- Pairs `(l,p)` in the small-prime branch: `1 ≤ l < H`, `p` prime,
`p ≤ floor (z^(1/100))`, and `p ∤ l`. -/
def taoSmallAntiSieveIndices (x H : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Ico 1 H).product (taoSmallAntiSievePrimeRange x)).filter
    fun lp => ¬lp.2 ∣ lp.1

theorem mem_taoSmallAntiSieveIndices {x H l p : ℕ} :
    (l, p) ∈ taoSmallAntiSieveIndices x H ↔
      1 ≤ l ∧ l < H ∧ Nat.Prime p ∧
        p ≤ taoSmallAntiSievePrimeCutoff x ∧ ¬p ∣ l := by
  simp [taoSmallAntiSieveIndices, mem_taoSmallAntiSievePrimeRange,
    and_assoc, and_left_comm, and_comm]

/-- One logarithmically weighted divisibility variable. -/
def taoSmallAntiSieveTerm
    (m' : ℕ) (lp : ℕ × ℕ) (ω : TaoPrimeTuple) : ℝ :=
  taoPrimeDivisibilityIndicator m' lp.1 lp.2 ω * Real.log lp.2

/-- The small-prime contribution in equation `(small-prime)`. -/
def taoSmallPrimeContribution
    (x H m' : ℕ) (ω : TaoPrimeTuple) : ℝ :=
  ∑ lp ∈ taoSmallAntiSieveIndices x H, taoSmallAntiSieveTerm m' lp ω

theorem taoSmallAntiSieveTerm_nonneg
    {x H : ℕ} {lp : ℕ × ℕ} (hlp : lp ∈ taoSmallAntiSieveIndices x H)
    (m' : ℕ) (ω : TaoPrimeTuple) :
    0 ≤ taoSmallAntiSieveTerm m' lp ω := by
  have hpPrime : Nat.Prime lp.2 :=
    (mem_taoSmallAntiSieveIndices.mp hlp).2.2.1
  exact mul_nonneg (taoPrimeDivisibilityIndicator_nonneg _ _ _ _)
    (Real.log_nonneg (by exact_mod_cast hpPrime.one_le))

theorem taoSmallPrimeContribution_nonneg
    (x H m' : ℕ) (ω : TaoPrimeTuple) :
    0 ≤ taoSmallPrimeContribution x H m' ω := by
  exact Finset.sum_nonneg fun lp hlp =>
    taoSmallAntiSieveTerm_nonneg hlp m' ω

/-- The joint divisibility event attached to an ordered 50-tuple of
small-prime shift pairs. -/
def TaoSmallPrimeJointDivisibilityEvent
    (m' : ℕ) (t : Fin 50 → ℕ × ℕ) (ω : TaoPrimeTuple) : Prop :=
  ∀ j, (t j).2 ∣ taoPrimeTupleStart m' ω + (t j).1

/-- The squarefree-modulus placeholder in the source character expansion:
the least common multiple of the 50 selected primes. -/
def taoSmallPrimeTupleModulus (t : Fin 50 → ℕ × ℕ) : ℕ :=
  Finset.univ.lcm fun j => (t j).2

/-- Two realizations of the same joint divisibility event have congruent
source products modulo each selected prime. -/
theorem taoSmallPrimeJointDivisibilityEvent_modEq
    {m' : ℕ} {t : Fin 50 → ℕ × ℕ} {ω₁ ω₂ : TaoPrimeTuple}
    (h₁ : TaoSmallPrimeJointDivisibilityEvent m' t ω₁)
    (h₂ : TaoSmallPrimeJointDivisibilityEvent m' t ω₂) (j : Fin 50) :
    taoPrimeTupleStart m' ω₁ ≡ taoPrimeTupleStart m' ω₂ [MOD (t j).2] := by
  exact Nat.ModEq.add_right_cancel' (t j).1
    ((h₁ j).modEq_zero_nat.trans (h₂ j).modEq_zero_nat.symm)

/-- Hence the event occupies at most one residue class modulo the lcm of the
50 selected primes. -/
theorem taoSmallPrimeJointDivisibilityEvent_modEq_lcm
    {m' : ℕ} {t : Fin 50 → ℕ × ℕ} {ω₁ ω₂ : TaoPrimeTuple}
    (h₁ : TaoSmallPrimeJointDivisibilityEvent m' t ω₁)
    (h₂ : TaoSmallPrimeJointDivisibilityEvent m' t ω₂) :
    taoPrimeTupleStart m' ω₁ ≡ taoPrimeTupleStart m' ω₂
      [MOD taoSmallPrimeTupleModulus t] := by
  by_cases hle : taoPrimeTupleStart m' ω₁ ≤ taoPrimeTupleStart m' ω₂
  · apply (Nat.modEq_iff_dvd' hle).2
    apply Finset.lcm_dvd
    intro j _hj
    exact (Nat.modEq_iff_dvd' hle).1
      (taoSmallPrimeJointDivisibilityEvent_modEq h₁ h₂ j)
  · have hle' : taoPrimeTupleStart m' ω₂ ≤ taoPrimeTupleStart m' ω₁ :=
      le_of_not_ge hle
    apply Nat.ModEq.symm
    apply (Nat.modEq_iff_dvd' hle').2
    apply Finset.lcm_dvd
    intro j _hj
    exact (Nat.modEq_iff_dvd' hle').1
      (taoSmallPrimeJointDivisibilityEvent_modEq h₂ h₁ j)

/-- Conversely, congruence to one realization modulo the tuple lcm forces
all 50 divisibility conditions. -/
theorem TaoSmallPrimeJointDivisibilityEvent.of_modEq_lcm
    {m' : ℕ} {t : Fin 50 → ℕ × ℕ} {ω₀ ω : TaoPrimeTuple}
    (h₀ : TaoSmallPrimeJointDivisibilityEvent m' t ω₀)
    (hω : taoPrimeTupleStart m' ω ≡ taoPrimeTupleStart m' ω₀
      [MOD taoSmallPrimeTupleModulus t]) :
    TaoSmallPrimeJointDivisibilityEvent m' t ω := by
  intro j
  have hpMod : taoPrimeTupleStart m' ω ≡ taoPrimeTupleStart m' ω₀
      [MOD (t j).2] :=
    hω.of_dvd (Finset.dvd_lcm (f := fun i : Fin 50 => (t i).2)
      (Finset.mem_univ j))
  exact Nat.modEq_zero_iff_dvd.mp
    ((hpMod.add_right (t j).1).trans (h₀ j).modEq_zero_nat)

/-- Exact CRT precursor used by the character expansion: the joint event is
either impossible or is precisely one residue-class fiber modulo the lcm.
The subsequent primitive-residue and character-average steps can therefore
work with a single class rather than 50 separate congruences. -/
theorem taoSmallPrimeJointDivisibilityEvent_empty_or_residueClass
    (m' : ℕ) (t : Fin 50 → ℕ × ℕ) :
    {ω : TaoPrimeTuple | TaoSmallPrimeJointDivisibilityEvent m' t ω} = ∅ ∨
      ∃ a : ℕ,
        {ω : TaoPrimeTuple | TaoSmallPrimeJointDivisibilityEvent m' t ω} =
          {ω | taoPrimeTupleStart m' ω ≡ a
            [MOD taoSmallPrimeTupleModulus t]} := by
  by_cases hE : ∃ ω : TaoPrimeTuple,
      TaoSmallPrimeJointDivisibilityEvent m' t ω
  · right
    obtain ⟨ω₀, hω₀⟩ := hE
    refine ⟨taoPrimeTupleStart m' ω₀, ?_⟩
    ext ω
    constructor
    · intro hω
      exact taoSmallPrimeJointDivisibilityEvent_modEq_lcm hω hω₀
    · intro hω
      exact hω₀.of_modEq_lcm hω
  · left
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact fun hω => hE ⟨ω, hω⟩

/-- For an actual ordered tuple from the small-prime expansion, every
realization is a unit modulo the tuple lcm.  The condition `p ∤ l` is exactly
what rules out a selected prime dividing the source product. -/
theorem TaoSmallPrimeJointDivisibilityEvent.coprime_modulus
    {x H m' : ℕ} {t : Fin 50 → ℕ × ℕ} {ω : TaoPrimeTuple}
    (ht : t ∈ Fintype.piFinset
      (fun _ : Fin 50 => taoSmallAntiSieveIndices x H))
    (hω : TaoSmallPrimeJointDivisibilityEvent m' t ω) :
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
  have hlMod : (t j).1 ≡ 0 [MOD (t j).2] := by
    simpa using (hpStart.modEq_zero_nat.add_right (t j).1).symm.trans
      (hω j).modEq_zero_nat
  exact hpNotL (Nat.modEq_zero_iff_dvd.mp hlMod)

/-- Source-ready refinement of the CRT precursor: for every ordered tuple in
the fiftieth-moment expansion, the joint event is either empty or a single
*primitive* residue-class fiber modulo the tuple lcm. -/
theorem taoSmallPrimeJointDivisibilityEvent_empty_or_primitiveResidueClass
    {x H : ℕ} (m' : ℕ) {t : Fin 50 → ℕ × ℕ}
    (ht : t ∈ Fintype.piFinset
      (fun _ : Fin 50 => taoSmallAntiSieveIndices x H)) :
    {ω : TaoPrimeTuple | TaoSmallPrimeJointDivisibilityEvent m' t ω} = ∅ ∨
      ∃ a : ℕ,
        Nat.Coprime a (taoSmallPrimeTupleModulus t) ∧
          {ω : TaoPrimeTuple | TaoSmallPrimeJointDivisibilityEvent m' t ω} =
            {ω | taoPrimeTupleStart m' ω ≡ a
              [MOD taoSmallPrimeTupleModulus t]} := by
  by_cases hE : ∃ ω : TaoPrimeTuple,
      TaoSmallPrimeJointDivisibilityEvent m' t ω
  · right
    obtain ⟨ω₀, hω₀⟩ := hE
    refine ⟨taoPrimeTupleStart m' ω₀, ?_, ?_⟩
    · exact (hω₀.coprime_modulus ht).symm
    · ext ω
      constructor
      · intro hω
        exact taoSmallPrimeJointDivisibilityEvent_modEq_lcm hω hω₀
      · intro hω
        exact hω₀.of_modEq_lcm hω
  · left
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact fun hω => hE ⟨ω, hω⟩

theorem prod_taoSmallAntiSieveTerm_eq
    (m' : ℕ) (t : Fin 50 → ℕ × ℕ) (ω : TaoPrimeTuple) :
    (∏ j, taoSmallAntiSieveTerm m' (t j) ω) =
      (∏ j, Real.log (t j).2) *
        if TaoSmallPrimeJointDivisibilityEvent m' t ω then 1 else 0 := by
  rw [show (∏ j, taoSmallAntiSieveTerm m' (t j) ω) =
      (∏ j, taoPrimeDivisibilityIndicator m' (t j).1 (t j).2 ω) *
        ∏ j, Real.log (t j).2 by
    simp only [taoSmallAntiSieveTerm, Finset.prod_mul_distrib]]
  by_cases h : TaoSmallPrimeJointDivisibilityEvent m' t ω
  · have hj : ∀ j, (t j).2 ∣ taoPrimeTupleStart m' ω + (t j).1 := h
    simp [taoPrimeDivisibilityIndicator, hj, h]
  · have hj : ∃ j, ¬(t j).2 ∣ taoPrimeTupleStart m' ω + (t j).1 := by
      simpa [TaoSmallPrimeJointDivisibilityEvent] using h
    obtain ⟨j, hj⟩ := hj
    have hzero :
        (∏ i, taoPrimeDivisibilityIndicator m' (t i).1 (t i).2 ω) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [taoPrimeDivisibilityIndicator, hj]
    rw [hzero]
    simp [h]

/-- Exact ordered-tuple expansion of the source's fixed fiftieth power. -/
theorem taoSmallPrimeContribution_pow_fifty
    (x H m' : ℕ) (ω : TaoPrimeTuple) :
    (taoSmallPrimeContribution x H m' ω) ^ (50 : ℕ) =
      ∑ t ∈ Fintype.piFinset
          (fun _ : Fin 50 => taoSmallAntiSieveIndices x H),
        (∏ j, Real.log (t j).2) *
          if TaoSmallPrimeJointDivisibilityEvent m' t ω then 1 else 0 := by
  unfold taoSmallPrimeContribution
  rw [Finset.sum_pow']
  apply Finset.sum_congr rfl
  intro t _ht
  exact prod_taoSmallAntiSieveTerm_eq m' t ω

/-- The literal real expectation in equation `(nsum)`. -/
def taoSmallPrimeFiftiethMoment
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (x H m' : ℕ) : ℝ :=
  ∫ ω, (taoSmallPrimeContribution x H m' ω) ^ (50 : ℕ)
    ∂taoPrimeTupleMeasure P hP

/-- Exact expectation expansion from equation `(nsum)`: the fiftieth moment
is a finite sum of logarithmic weights times joint divisibility
probabilities. -/
theorem taoSmallPrimeFiftiethMoment_eq_sum_jointProbabilities
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (x H m' : ℕ) :
    taoSmallPrimeFiftiethMoment P hP x H m' =
      ∑ t ∈ Fintype.piFinset
          (fun _ : Fin 50 => taoSmallAntiSieveIndices x H),
        (∏ j, Real.log (t j).2) *
          (taoPrimeTupleMeasure P hP).real
            {ω | TaoSmallPrimeJointDivisibilityEvent m' t ω} := by
  let S := Fintype.piFinset
    (fun _ : Fin 50 => taoSmallAntiSieveIndices x H)
  have hmeas : ∀ t : Fin 50 → ℕ × ℕ,
      MeasurableSet {ω : TaoPrimeTuple |
        TaoSmallPrimeJointDivisibilityEvent m' t ω} := by
    intro t
    exact (Set.to_countable _).measurableSet
  have hterm : ∀ t : Fin 50 → ℕ × ℕ,
      Integrable
        (fun ω => (∏ j, Real.log (t j).2) *
          if TaoSmallPrimeJointDivisibilityEvent m' t ω then 1 else 0)
        (taoPrimeTupleMeasure P hP) := by
    intro t
    have hi : Integrable
        ({ω : TaoPrimeTuple | TaoSmallPrimeJointDivisibilityEvent m' t ω}.indicator
          (fun _ => (1 : ℝ))) (taoPrimeTupleMeasure P hP) :=
      (integrable_const (1 : ℝ)).indicator (hmeas t)
    simpa only [Set.indicator, Set.mem_setOf_eq] using
      hi.const_mul (∏ j, Real.log (t j).2)
  unfold taoSmallPrimeFiftiethMoment
  calc
    (∫ ω, (taoSmallPrimeContribution x H m' ω) ^ (50 : ℕ)
        ∂taoPrimeTupleMeasure P hP) =
        ∫ ω, ∑ t ∈ S,
          (∏ j, Real.log (t j).2) *
            if TaoSmallPrimeJointDivisibilityEvent m' t ω then 1 else 0
          ∂taoPrimeTupleMeasure P hP := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω =>
        taoSmallPrimeContribution_pow_fifty x H m' ω
    _ = ∑ t ∈ S, ∫ ω,
          (∏ j, Real.log (t j).2) *
            if TaoSmallPrimeJointDivisibilityEvent m' t ω then 1 else 0
          ∂taoPrimeTupleMeasure P hP := by
      exact integral_finsetSum S fun t ht => hterm t
    _ = ∑ t ∈ S,
        (∏ j, Real.log (t j).2) *
          (taoPrimeTupleMeasure P hP).real
            {ω | TaoSmallPrimeJointDivisibilityEvent m' t ω} := by
      apply Finset.sum_congr rfl
      intro t _ht
      rw [show (fun ω : TaoPrimeTuple =>
          (∏ j, Real.log (t j).2) *
            if TaoSmallPrimeJointDivisibilityEvent m' t ω then 1 else 0) =
          fun ω => (∏ j, Real.log (t j).2) *
            {ω : TaoPrimeTuple |
              TaoSmallPrimeJointDivisibilityEvent m' t ω}.indicator
                (fun _ => (1 : ℝ)) ω by
        funext ω
        simp only [Set.indicator, Set.mem_setOf_eq]
        ]
      rw [integral_const_mul]
      change (∏ j, Real.log (t j).2) *
          (∫ ω : TaoPrimeTuple,
            {ω : TaoPrimeTuple |
              TaoSmallPrimeJointDivisibilityEvent m' t ω}.indicator 1 ω
              ∂taoPrimeTupleMeasure P hP) = _
      rw [integral_indicator_one (hmeas t)]

end

end Tao2026
