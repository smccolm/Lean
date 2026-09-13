import Tao2026.BadIntervalCharacterExpansion

/-!
# Normalized prime character sums and the exceptional threshold

This module begins the source-faithful formalization of Section 5.  It names
Tao's normalized prime character sum, the exact decimal threshold
`Z^(-0.008) = Z^(-1/125)`, and the finite set of nonprincipal primitive
characters exceeding that threshold.  The elementary unexceptional
1000th-moment saving is proved here; bounding the exceptional set is the
analytic content of Lemma 5.1.
-/

namespace Tao2026

open scoped Classical

noncomputable section

/-- Tao's normalized prime character sum `s_Z(χ)`. -/
abbrev taoNormalizedPrimeCharacterSum
    {q : ℕ} (χ : DirichletCharacter ℂ q) (Z : ℕ) : ℂ :=
  taoDyadicPrimeCharacterAverage χ Z

/-- Changing the level of a Dirichlet character does not change its value on
an integer coprime to the new level. -/
theorem changeLevel_apply_natCast_of_coprime
    {d q n : ℕ} (χ : DirichletCharacter ℂ d) (hd : d ∣ q)
    (hn : Nat.Coprime n q) :
    (DirichletCharacter.changeLevel hd χ) (n : ZMod q) =
      χ (n : ZMod d) := by
  have h := DirichletCharacter.changeLevel_eq_cast_of_dvd χ hd
    (ZMod.unitOfCoprime n hn)
  simp only [ZMod.coe_unitOfCoprime] at h
  rw [ZMod.cast_natCast hd n] at h
  exact h

/-- On a prime band coprime to the ambient level, a character and its
primitive counterpart have exactly the same normalized prime sum.  This is
the rigorous form of the source footnote justifying conductor replacement. -/
theorem taoNormalizedPrimeCharacterSum_eq_primitiveCharacter
    {q Z : ℕ} (χ : DirichletCharacter ℂ q)
    (hcoprime : ∀ p ∈ taoDyadicPrimeBand Z, Nat.Coprime p q) :
    taoNormalizedPrimeCharacterSum χ Z =
      taoNormalizedPrimeCharacterSum χ.primitiveCharacter Z := by
  unfold taoNormalizedPrimeCharacterSum taoDyadicPrimeCharacterAverage
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  calc
    χ (p : ZMod q) =
        (DirichletCharacter.changeLevel χ.conductor_dvd_level
          χ.primitiveCharacter) (p : ZMod q) := by
      exact congrArg (fun ψ : DirichletCharacter ℂ q => ψ (p : ZMod q))
        χ.changeLevel_primitiveCharacter.symm
    _ = χ.primitiveCharacter (p : ZMod χ.conductor) :=
      changeLevel_apply_natCast_of_coprime χ.primitiveCharacter
        χ.conductor_dvd_level (hcoprime p hp)

/-- A nonprincipal character has a nonprincipal primitive counterpart. -/
theorem primitiveCharacter_ne_one_of_ne_one
    {q : ℕ} (χ : DirichletCharacter ℂ q) [NeZero q] (hχ : χ ≠ 1) :
    χ.primitiveCharacter ≠ 1 := by
  intro hPrimitive
  apply hχ
  rw [← χ.changeLevel_primitiveCharacter, hPrimitive,
    DirichletCharacter.changeLevel_one]

/-- When every prime in the band is coprime to `q`, the principal normalized
prime sum is exactly one. -/
theorem taoNormalizedPrimeCharacterSum_one_eq_one
    {q Z : ℕ} (hZ : (taoDyadicPrimeBand Z).Nonempty)
    (hcoprime : ∀ p ∈ taoDyadicPrimeBand Z, Nat.Coprime p q) :
    taoNormalizedPrimeCharacterSum (1 : DirichletCharacter ℂ q) Z = 1 := by
  unfold taoNormalizedPrimeCharacterSum taoDyadicPrimeCharacterAverage
  have hsum :
      (∑ p ∈ taoDyadicPrimeBand Z,
          (1 : DirichletCharacter ℂ q) (p : ZMod q)) =
        ∑ _p ∈ taoDyadicPrimeBand Z, (1 : ℂ) := by
    apply Finset.sum_congr rfl
    intro p hp
    exact MulChar.one_apply
      ((ZMod.isUnit_iff_coprime p q).mpr (hcoprime p hp))
  rw [hsum]
  simp [Finset.card_ne_zero.mpr hZ]

/-- The finite set of all nonprincipal characters modulo `q`. -/
def taoNonprincipalCharacters (q : ℕ) :
    Finset (DirichletCharacter ℂ q) :=
  Finset.univ.erase 1

theorem mem_taoNonprincipalCharacters
    {q : ℕ} {χ : DirichletCharacter ℂ q} :
    χ ∈ taoNonprincipalCharacters q ↔ χ ≠ 1 := by
  simp [taoNonprincipalCharacters]

/-- Exact separation of the principal character from the complete 1000th
moment.  The principal term contributes precisely one. -/
theorem sum_allPrimeCharacter_pow_thousand_eq_one_add_nonprincipal
    (q Z : ℕ) (hZ : (taoDyadicPrimeBand Z).Nonempty)
    (hcoprime : ∀ p ∈ taoDyadicPrimeBand Z, Nat.Coprime p q) :
    (∑ χ : DirichletCharacter ℂ q,
        ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (1000 : ℕ)) =
      1 + ∑ χ ∈ taoNonprincipalCharacters q,
        ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (1000 : ℕ) := by
  unfold taoNonprincipalCharacters
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ
    (1 : DirichletCharacter ℂ q))]
  rw [taoNormalizedPrimeCharacterSum_one_eq_one hZ hcoprime]
  simp [add_comm]

/-- A prime strictly larger than every prime entering a finite lcm is coprime
to that lcm. -/
theorem prime_coprime_finset_lcm_of_prime_lt
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℕ) {p : ℕ}
    (hp : Nat.Prime p) (hf : ∀ i ∈ s, Nat.Prime (f i))
    (hlt : ∀ i ∈ s, f i < p) :
    Nat.Coprime p (s.lcm f) := by
  rw [hp.coprime_iff_not_dvd]
  induction s using Finset.induction_on with
  | empty => simpa using hp.not_dvd_one
  | @insert a s ha ih =>
      rw [Finset.lcm_insert]
      apply hp.not_dvd_lcm
      · intro hpa
        rcases (Nat.dvd_prime (hf a (Finset.mem_insert_self a s))).mp hpa with
          hpOne | hpEq
        · exact hp.ne_one hpOne
        · exact (ne_of_gt (hlt a (Finset.mem_insert_self a s))) hpEq
      · exact ih
          (fun i hi => hf i (Finset.mem_insert_of_mem hi))
          (fun i hi => hlt i (Finset.mem_insert_of_mem hi))

/-- Every prime in a dyadic band beginning above the small-prime cutoff is
coprime to an actual ordered-tuple modulus. -/
theorem coprime_taoSmallPrimeTupleModulus_of_mem_dyadicBand
    {x H P p : ℕ} {t : Fin 50 → ℕ × ℕ}
    (ht : t ∈ Fintype.piFinset
      (fun _ : Fin 50 => taoSmallAntiSieveIndices x H))
    (hcutoff : taoSmallAntiSievePrimeCutoff x < P)
    (hp : p ∈ taoDyadicPrimeBand P) :
    Nat.Coprime p (taoSmallPrimeTupleModulus t) := by
  have hpData := mem_taoDyadicPrimeBand.mp hp
  unfold taoSmallPrimeTupleModulus
  apply prime_coprime_finset_lcm_of_prime_lt
    (Finset.univ : Finset (Fin 50)) (fun j => (t j).2) hpData.1
  · intro j _hj
    exact (mem_taoSmallAntiSieveIndices.mp
      (Fintype.mem_piFinset.mp ht j)).2.2.1
  · intro j _hj
    have hjBound := (mem_taoSmallAntiSieveIndices.mp
      (Fintype.mem_piFinset.mp ht j)).2.2.2.1
    exact lt_of_le_of_lt hjBound (hcutoff.trans_le hpData.2.1)

/-- For every modulus occurring in the ordered fiftieth-moment expansion,
the normalized character sum on a separated dyadic band agrees exactly with
the sum of the associated primitive character. -/
theorem taoNormalizedPrimeCharacterSum_tupleModulus_eq_primitiveCharacter
    {x H P : ℕ} {t : Fin 50 → ℕ × ℕ}
    (ht : t ∈ Fintype.piFinset
      (fun _ : Fin 50 => taoSmallAntiSieveIndices x H))
    (hcutoff : taoSmallAntiSievePrimeCutoff x < P)
    (χ : DirichletCharacter ℂ (taoSmallPrimeTupleModulus t)) :
    taoNormalizedPrimeCharacterSum χ P =
      taoNormalizedPrimeCharacterSum χ.primitiveCharacter P := by
  apply taoNormalizedPrimeCharacterSum_eq_primitiveCharacter χ
  intro p hp
  exact coprime_taoSmallPrimeTupleModulus_of_mem_dyadicBand
    ht hcutoff hp

/-- The nonprincipal 1000th moment after each ambient character has been
replaced by its primitive counterpart at its conductor.  Keeping the original
finite index avoids any dependent-type coercion while exposing the precise
primitive character to which Lemma 5.1 applies. -/
def taoPrimitiveCounterpartMomentSum (q Z : ℕ) : ℝ :=
  ∑ χ ∈ taoNonprincipalCharacters q,
    ‖taoNormalizedPrimeCharacterSum χ.primitiveCharacter Z‖ ^ (1000 : ℕ)

/-- Exact first conductor-regrouping step: on a band coprime to the ambient
modulus, replacing every nonprincipal character by its primitive counterpart
does not change the moment sum. -/
theorem sum_nonprincipalPrimeCharacter_pow_thousand_eq_primitiveCounterparts
    (q Z : ℕ)
    (hcoprime : ∀ p ∈ taoDyadicPrimeBand Z, Nat.Coprime p q) :
    (∑ χ ∈ taoNonprincipalCharacters q,
        ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (1000 : ℕ)) =
      taoPrimitiveCounterpartMomentSum q Z := by
  unfold taoPrimitiveCounterpartMomentSum
  apply Finset.sum_congr rfl
  intro χ _hχ
  rw [taoNormalizedPrimeCharacterSum_eq_primitiveCharacter χ hcoprime]

/-- Ambient characters whose exact conductor is `d`. -/
def TaoCharacterOfConductor (q d : ℕ) :=
  {χ : DirichletCharacter ℂ q // χ.conductor = d}

namespace TaoCharacterOfConductor

/-- The fixed conductor divides the ambient level. -/
theorem conductor_dvd_level {q d : ℕ} (χ : TaoCharacterOfConductor q d) :
    d ∣ q := by
  rw [← χ.property]
  exact χ.1.conductor_dvd_level

/-- The primitive counterpart transported to the stated fixed conductor. -/
noncomputable def primitiveCharacter {q d : ℕ}
    (χ : TaoCharacterOfConductor q d) : DirichletCharacter ℂ d :=
  χ.property ▸ χ.1.primitiveCharacter

/-- The fixed-conductor counterpart is primitive. -/
theorem primitiveCharacter_isPrimitive {q d : ℕ}
    (χ : TaoCharacterOfConductor q d) :
    DirichletCharacter.IsPrimitive χ.primitiveCharacter := by
  rcases χ with ⟨χ, hχ⟩
  subst d
  exact χ.primitiveCharacter_isPrimitive

/-- Lifting the fixed-conductor counterpart recovers the ambient character. -/
theorem changeLevel_primitiveCharacter {q d : ℕ}
    (χ : TaoCharacterOfConductor q d) :
    DirichletCharacter.changeLevel χ.conductor_dvd_level
      χ.primitiveCharacter = χ.1 := by
  rcases χ with ⟨χ, hχ⟩
  subst d
  exact χ.changeLevel_primitiveCharacter

/-- Within a fixed conductor fiber, primitive counterparts are injective. -/
theorem primitiveCharacter_injective {q d : ℕ} :
    Function.Injective
      (@primitiveCharacter q d) := by
  intro χ ψ h
  apply Subtype.ext
  calc
    χ.1 = DirichletCharacter.changeLevel χ.conductor_dvd_level
        χ.primitiveCharacter := χ.changeLevel_primitiveCharacter.symm
    _ = DirichletCharacter.changeLevel ψ.conductor_dvd_level
        ψ.primitiveCharacter := by rw [h]
    _ = ψ.1 := ψ.changeLevel_primitiveCharacter

/-- A fixed conductor other than one yields a nonprincipal primitive
counterpart. -/
theorem primitiveCharacter_ne_one {q d : ℕ}
    [NeZero q] (χ : TaoCharacterOfConductor q d) (hd : d ≠ 1) :
    χ.primitiveCharacter ≠ 1 := by
  have hd0 : d ≠ 0 := by
    rw [← χ.property]
    exact χ.1.conductor_ne_zero
  letI : NeZero d := ⟨hd0⟩
  intro hOne
  have hConductor : χ.primitiveCharacter.conductor = d :=
    χ.primitiveCharacter_isPrimitive
  rw [hOne, DirichletCharacter.conductor_one] at hConductor
  exact hd hConductor.symm

end TaoCharacterOfConductor

/-- Finite ambient character fiber of exact conductor `d`. -/
def taoCharactersOfConductor (q d : ℕ) :
    Finset (DirichletCharacter ℂ q) :=
  Finset.univ.filter fun χ => χ.conductor = d

theorem mem_taoCharactersOfConductor
    {q d : ℕ} {χ : DirichletCharacter ℂ q} :
    χ ∈ taoCharactersOfConductor q d ↔ χ.conductor = d := by
  simp [taoCharactersOfConductor]

/-- Primitive counterpart of one member of the finite conductor fiber. -/
noncomputable def taoPrimitiveCharacterOfConductorElement
    {q d : ℕ} (χ : ↥(taoCharactersOfConductor q d)) :
    DirichletCharacter ℂ d :=
  TaoCharacterOfConductor.primitiveCharacter
    ⟨χ.1, mem_taoCharactersOfConductor.mp χ.2⟩

/-- The primitive-counterpart map is injective on each fixed conductor
fiber. -/
theorem taoPrimitiveCharacterOfConductorElement_injective
    (q d : ℕ) :
    Function.Injective
      (@taoPrimitiveCharacterOfConductorElement q d) := by
  intro χ ψ h
  have hFiber :
      (⟨χ.1, mem_taoCharactersOfConductor.mp χ.2⟩ :
          TaoCharacterOfConductor q d) =
        ⟨ψ.1, mem_taoCharactersOfConductor.mp ψ.2⟩ :=
    TaoCharacterOfConductor.primitiveCharacter_injective h
  have hValue : χ.1 = ψ.1 :=
    congrArg (fun ξ : TaoCharacterOfConductor q d => ξ.1) hFiber
  exact Subtype.ext hValue

/-- Image of the ambient conductor-`d` fiber in the primitive characters of
level `d`. -/
noncomputable def taoFixedConductorPrimitiveCharacters (q d : ℕ) :
    Finset (DirichletCharacter ℂ d) :=
  (taoCharactersOfConductor q d).attach.image
    taoPrimitiveCharacterOfConductorElement

/-- The exact exceptional threshold `Z^(-0.008)`, written without a decimal
approximation as `Z^(-1/125)`. -/
def taoExceptionalPrimeCharacterThreshold (Z : ℕ) : ℝ :=
  (Z : ℝ) ^ (-(1 : ℝ) / 125)

/-- A nonprincipal primitive character is exceptional at scale `Z` exactly
when its normalized prime sum reaches Tao's `Z^(-0.008)` threshold. -/
def IsTaoExceptionalPrimeCharacter
    {q : ℕ} (Z : ℕ) (χ : DirichletCharacter ℂ q) : Prop :=
  DirichletCharacter.IsPrimitive χ ∧ χ ≠ 1 ∧
    taoExceptionalPrimeCharacterThreshold Z ≤
      ‖taoNormalizedPrimeCharacterSum χ Z‖

/-- The literal finite collection of exceptional primitive characters at a
fixed level and prime scale. -/
def taoExceptionalPrimitiveCharacters (q Z : ℕ) :
    Finset (DirichletCharacter ℂ q) :=
  Finset.univ.filter (IsTaoExceptionalPrimeCharacter Z)

theorem mem_taoExceptionalPrimitiveCharacters
    {q Z : ℕ} {χ : DirichletCharacter ℂ q} :
    χ ∈ taoExceptionalPrimitiveCharacters q Z ↔
      DirichletCharacter.IsPrimitive χ ∧ χ ≠ 1 ∧
        taoExceptionalPrimeCharacterThreshold Z ≤
          ‖taoNormalizedPrimeCharacterSum χ Z‖ := by
  simp [taoExceptionalPrimitiveCharacters,
    IsTaoExceptionalPrimeCharacter]

/-- The exceptional threshold is nonnegative. -/
theorem taoExceptionalPrimeCharacterThreshold_nonneg (Z : ℕ) :
    0 ≤ taoExceptionalPrimeCharacterThreshold Z := by
  exact Real.rpow_nonneg (Nat.cast_nonneg Z) _

/-- Raising Tao's exact threshold to the 1000th power gives the source saving
`Z^(-8)` with no rounding of the decimal exponent. -/
theorem taoExceptionalPrimeCharacterThreshold_pow_thousand
    (Z : ℕ) :
    taoExceptionalPrimeCharacterThreshold Z ^ (1000 : ℕ) =
      (Z : ℝ) ^ (-(8 : ℝ)) := by
  unfold taoExceptionalPrimeCharacterThreshold
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg Z)]
  congr 1
  norm_num

/-- Every normalized prime character sum has modulus at most one whenever
the dyadic prime band is nonempty. -/
theorem norm_taoNormalizedPrimeCharacterSum_le_one
    {q Z : ℕ} (χ : DirichletCharacter ℂ q)
    (hZ : (taoDyadicPrimeBand Z).Nonempty) :
    ‖taoNormalizedPrimeCharacterSum χ Z‖ ≤ 1 := by
  let P : Fin 1001 → ℕ := fun _ => Z
  have hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty := fun _ => hZ
  have hEq : taoPrimeCoordinateCharacterExpectation P hP χ (1 : Fin 1001) =
      taoNormalizedPrimeCharacterSum χ Z := by
    rw [taoPrimeCoordinateCharacterExpectation_eq_dyadicAverage]
    rw [taoDyadicPrimeCoordinateCharacterAverage_eq_characterAverage]
    norm_num
  rw [← hEq]
  exact norm_taoPrimeCoordinateCharacterExpectation_le_one P hP χ 1

/-- A primitive nonprincipal character outside the exceptional set satisfies
the strict source threshold bound. -/
theorem norm_taoNormalizedPrimeCharacterSum_lt_threshold_of_not_exceptional
    {q Z : ℕ} {χ : DirichletCharacter ℂ q}
    (hPrimitive : DirichletCharacter.IsPrimitive χ) (hNonprincipal : χ ≠ 1)
    (hχ : χ ∉ taoExceptionalPrimitiveCharacters q Z) :
    ‖taoNormalizedPrimeCharacterSum χ Z‖ <
      taoExceptionalPrimeCharacterThreshold Z := by
  rw [mem_taoExceptionalPrimitiveCharacters] at hχ
  simpa [hPrimitive, hNonprincipal] using hχ

/-- The source's elementary unexceptional contribution: the 1000th power of
an unexceptional normalized prime sum is strictly smaller than `Z^(-8)`. -/
theorem norm_taoNormalizedPrimeCharacterSum_pow_thousand_lt
    {q Z : ℕ} {χ : DirichletCharacter ℂ q}
    (hPrimitive : DirichletCharacter.IsPrimitive χ) (hNonprincipal : χ ≠ 1)
    (hχ : χ ∉ taoExceptionalPrimitiveCharacters q Z) :
    ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (1000 : ℕ) <
      (Z : ℝ) ^ (-(8 : ℝ)) := by
  calc
    ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (1000 : ℕ) <
        taoExceptionalPrimeCharacterThreshold Z ^ (1000 : ℕ) := by
      exact pow_lt_pow_left₀
        (norm_taoNormalizedPrimeCharacterSum_lt_threshold_of_not_exceptional
          hPrimitive hNonprincipal hχ)
        (norm_nonneg _) (by norm_num)
    _ = (Z : ℝ) ^ (-(8 : ℝ)) :=
      taoExceptionalPrimeCharacterThreshold_pow_thousand Z

/-- Primitive nonprincipal characters below the exceptional threshold. -/
def taoUnexceptionalPrimitiveCharacters (q Z : ℕ) :
    Finset (DirichletCharacter ℂ q) :=
  Finset.univ.filter fun χ =>
    DirichletCharacter.IsPrimitive χ ∧ χ ≠ 1 ∧
      χ ∉ taoExceptionalPrimitiveCharacters q Z

/-- All primitive nonprincipal characters modulo `q`.  This is the finite
ambient set split into exceptional and unexceptional characters below. -/
def taoPrimitiveNonprincipalCharacters (q : ℕ) :
    Finset (DirichletCharacter ℂ q) :=
  Finset.univ.filter fun χ => DirichletCharacter.IsPrimitive χ ∧ χ ≠ 1

theorem mem_taoPrimitiveNonprincipalCharacters
    {q : ℕ} {χ : DirichletCharacter ℂ q} :
    χ ∈ taoPrimitiveNonprincipalCharacters q ↔
      DirichletCharacter.IsPrimitive χ ∧ χ ≠ 1 := by
  simp [taoPrimitiveNonprincipalCharacters]

/-- For positive ambient level and `d ≠ 1`, the fixed-conductor image lies
inside the primitive nonprincipal characters of level `d`. -/
theorem taoFixedConductorPrimitiveCharacters_subset
    (q d : ℕ) [NeZero q] (hd : d ≠ 1) :
    taoFixedConductorPrimitiveCharacters q d ⊆
      taoPrimitiveNonprincipalCharacters d := by
  intro ψ hψ
  rcases Finset.mem_image.mp hψ with ⟨χ, _hχ, rfl⟩
  rw [mem_taoPrimitiveNonprincipalCharacters]
  let χd : TaoCharacterOfConductor q d :=
    ⟨χ.1, mem_taoCharactersOfConductor.mp χ.2⟩
  exact ⟨χd.primitiveCharacter_isPrimitive,
    χd.primitiveCharacter_ne_one hd⟩

/-- A fixed ambient conductor fiber contributes no more than the full
primitive nonprincipal 1000th moment at that conductor. -/
theorem sum_fixedConductorPrimitiveCharacter_pow_thousand_le
    (q d Z : ℕ) [NeZero q] (hd : d ≠ 1) :
    (∑ ψ ∈ taoFixedConductorPrimitiveCharacters q d,
        ‖taoNormalizedPrimeCharacterSum ψ Z‖ ^ (1000 : ℕ)) ≤
      ∑ ψ ∈ taoPrimitiveNonprincipalCharacters d,
        ‖taoNormalizedPrimeCharacterSum ψ Z‖ ^ (1000 : ℕ) := by
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (taoFixedConductorPrimitiveCharacters_subset q d hd)
    (fun ψ _hψ _hnot => pow_nonneg (norm_nonneg _) _)

/-- The literal 1000th moment of the primitive counterparts in one fixed
ambient conductor fiber. -/
noncomputable def taoFixedConductorPrimitiveMomentSum
    (q d Z : ℕ) : ℝ :=
  ∑ χ ∈ (taoCharactersOfConductor q d).attach,
    ‖taoNormalizedPrimeCharacterSum
      (taoPrimitiveCharacterOfConductorElement χ) Z‖ ^ (1000 : ℕ)

/-- Reindexing a fixed conductor fiber by its injective primitive-character
image preserves its moment sum exactly. -/
theorem taoFixedConductorPrimitiveMomentSum_eq_image
    (q d Z : ℕ) :
    taoFixedConductorPrimitiveMomentSum q d Z =
      ∑ ψ ∈ taoFixedConductorPrimitiveCharacters q d,
        ‖taoNormalizedPrimeCharacterSum ψ Z‖ ^ (1000 : ℕ) := by
  unfold taoFixedConductorPrimitiveMomentSum
  rw [taoFixedConductorPrimitiveCharacters, Finset.sum_image
    (taoPrimitiveCharacterOfConductorElement_injective q d).injOn]

/-- Transporting a primitive counterpart to its named conductor does not
alter the normalized sum. -/
theorem taoNormalizedPrimeCharacterSum_primitiveConductorElement
    {q d Z : ℕ} (χ : ↥(taoCharactersOfConductor q d)) :
    taoNormalizedPrimeCharacterSum
        (taoPrimitiveCharacterOfConductorElement χ) Z =
      taoNormalizedPrimeCharacterSum χ.1.primitiveCharacter Z := by
  rcases χ with ⟨χ, hχ⟩
  have hConductor := mem_taoCharactersOfConductor.mp hχ
  subst d
  rfl

/-- For positive ambient level and `d ≠ 1`, the exact-conductor fiber is the
`d`-fiber inside the nonprincipal characters. -/
theorem taoCharactersOfConductor_eq_filter_nonprincipal
    (q d : ℕ) [NeZero q] (hd : d ≠ 1) :
    taoCharactersOfConductor q d =
      (taoNonprincipalCharacters q).filter fun χ => χ.conductor = d := by
  ext χ
  rw [mem_taoCharactersOfConductor, Finset.mem_filter,
    mem_taoNonprincipalCharacters]
  constructor
  · intro hConductor
    refine ⟨?_, hConductor⟩
    intro hOne
    have : χ.conductor = 1 :=
      (DirichletCharacter.eq_one_iff_conductor_eq_one).mp hOne
    exact hd (hConductor.symm.trans this)
  · exact fun h => h.2

/-- On a band coprime to the ambient modulus, one fixed conductor fiber of
ambient moments is exactly the corresponding fixed primitive moment sum. -/
theorem sum_filter_conductorPrimeCharacter_pow_thousand_eq_fixed
    (q d Z : ℕ) [NeZero q] (hd : d ≠ 1)
    (hcoprime : ∀ p ∈ taoDyadicPrimeBand Z, Nat.Coprime p q) :
    (∑ χ ∈ (taoNonprincipalCharacters q).filter
          (fun χ => χ.conductor = d),
        ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (1000 : ℕ)) =
      taoFixedConductorPrimitiveMomentSum q d Z := by
  rw [← taoCharactersOfConductor_eq_filter_nonprincipal q d hd]
  unfold taoFixedConductorPrimitiveMomentSum
  rw [← Finset.sum_attach (taoCharactersOfConductor q d)
    (fun χ => ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (1000 : ℕ))]
  apply Finset.sum_congr rfl
  intro χ _hχ
  rw [taoNormalizedPrimeCharacterSum_primitiveConductorElement]
  rw [← taoNormalizedPrimeCharacterSum_eq_primitiveCharacter χ.1 hcoprime]

/-- Exact finite regrouping of the entire nonprincipal moment by the
positive divisors `d ≠ 1` of the ambient modulus. -/
theorem sum_nonprincipalPrimeCharacter_pow_thousand_eq_sum_fixedConductors
    (q Z : ℕ) (hq : 0 < q)
    (hcoprime : ∀ p ∈ taoDyadicPrimeBand Z, Nat.Coprime p q) :
    (∑ χ ∈ taoNonprincipalCharacters q,
        ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (1000 : ℕ)) =
      ∑ d ∈ q.divisors.erase 1,
        taoFixedConductorPrimitiveMomentSum q d Z := by
  letI : NeZero q := ⟨hq.ne'⟩
  let f : DirichletCharacter ℂ q → ℝ := fun χ =>
    ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (1000 : ℕ)
  have hMaps : ∀ χ ∈ taoNonprincipalCharacters q,
      χ.conductor ∈ q.divisors.erase 1 := by
    intro χ hχ
    rw [Finset.mem_erase, Nat.mem_divisors]
    have hNonprincipal : χ ≠ 1 := mem_taoNonprincipalCharacters.mp hχ
    have hConductorOne : χ.conductor ≠ 1 := by
      intro hOne
      exact hNonprincipal
        (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr hOne)
    exact ⟨hConductorOne, χ.conductor_dvd_level, hq.ne'⟩
  have hFiber := Finset.sum_fiberwise_of_maps_to hMaps f
  calc
    (∑ χ ∈ taoNonprincipalCharacters q,
        ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (1000 : ℕ)) =
        ∑ d ∈ q.divisors.erase 1,
          ∑ χ ∈ taoNonprincipalCharacters q with χ.conductor = d,
            f χ := by
      simpa only [f] using hFiber.symm
    _ = ∑ d ∈ q.divisors.erase 1,
        taoFixedConductorPrimitiveMomentSum q d Z := by
      apply Finset.sum_congr rfl
      intro d hd
      exact sum_filter_conductorPrimeCharacter_pow_thousand_eq_fixed
        q d Z (Finset.ne_of_mem_erase hd) hcoprime

theorem mem_taoUnexceptionalPrimitiveCharacters
    {q Z : ℕ} {χ : DirichletCharacter ℂ q} :
    χ ∈ taoUnexceptionalPrimitiveCharacters q Z ↔
      DirichletCharacter.IsPrimitive χ ∧ χ ≠ 1 ∧
        χ ∉ taoExceptionalPrimitiveCharacters q Z := by
  simp [taoUnexceptionalPrimitiveCharacters]

/-- The exceptional and unexceptional definitions form an exact partition
of the primitive nonprincipal characters. -/
theorem taoPrimitiveNonprincipalCharacters_eq_exceptional_union_unexceptional
    (q Z : ℕ) :
    taoPrimitiveNonprincipalCharacters q =
      taoExceptionalPrimitiveCharacters q Z ∪
        taoUnexceptionalPrimitiveCharacters q Z := by
  ext χ
  rw [mem_taoPrimitiveNonprincipalCharacters, Finset.mem_union,
    mem_taoExceptionalPrimitiveCharacters,
    mem_taoUnexceptionalPrimitiveCharacters]
  constructor
  · intro hχ
    by_cases hExceptional :
        χ ∈ taoExceptionalPrimitiveCharacters q Z
    · exact Or.inl (mem_taoExceptionalPrimitiveCharacters.mp hExceptional)
    · exact Or.inr ⟨hχ.1, hχ.2, hExceptional⟩
  · rintro (hExceptional | hUnexceptional)
    · exact ⟨hExceptional.1, hExceptional.2.1⟩
    · exact ⟨hUnexceptional.1, hUnexceptional.2.1⟩

/-- The two sides of the exceptional/unexceptional partition are disjoint. -/
theorem taoExceptionalPrimitiveCharacters_disjoint_unexceptional
    (q Z : ℕ) :
    Disjoint (taoExceptionalPrimitiveCharacters q Z)
      (taoUnexceptionalPrimitiveCharacters q Z) := by
  rw [Finset.disjoint_left]
  intro χ hExceptional hUnexceptional
  exact (mem_taoUnexceptionalPrimitiveCharacters.mp hUnexceptional).2.2
    hExceptional

/-- On a nonempty prime band, the 1000th moment of any normalized character
sum is bounded by its square.  This converts the exceptional contribution to
the squared moment appearing in Lemma 5.1. -/
theorem norm_taoNormalizedPrimeCharacterSum_pow_thousand_le_sq
    {q Z : ℕ} (χ : DirichletCharacter ℂ q)
    (hZ : (taoDyadicPrimeBand Z).Nonempty) :
    ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (1000 : ℕ) ≤
      ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (2 : ℕ) := by
  have hnorm := norm_taoNormalizedPrimeCharacterSum_le_one χ hZ
  calc
    ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (1000 : ℕ) =
        ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (2 : ℕ) *
          ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (998 : ℕ) := by
      rw [← pow_add]
    _ ≤ ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (2 : ℕ) * 1 := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_one₀ (norm_nonneg _) hnorm) (sq_nonneg _)
    _ = ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (2 : ℕ) := by
      rw [mul_one]

/-- The exceptional 1000th moment is no larger than the exceptional squared
moment which Lemma 5.1 estimates. -/
theorem sum_exceptionalPrimeCharacter_pow_thousand_le_sum_sq
    (q Z : ℕ) (hZ : (taoDyadicPrimeBand Z).Nonempty) :
    (∑ χ ∈ taoExceptionalPrimitiveCharacters q Z,
        ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (1000 : ℕ)) ≤
      ∑ χ ∈ taoExceptionalPrimitiveCharacters q Z,
        ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (2 : ℕ) := by
  exact Finset.sum_le_sum fun χ _hχ =>
    norm_taoNormalizedPrimeCharacterSum_pow_thousand_le_sq χ hZ

/-- The finite sum of unexceptional 1000th moments is bounded by its
cardinality times the exact `Z^(-8)` saving. -/
theorem sum_unexceptionalPrimeCharacter_pow_thousand_le_card_mul
    (q Z : ℕ) :
    (∑ χ ∈ taoUnexceptionalPrimitiveCharacters q Z,
        ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (1000 : ℕ)) ≤
      (taoUnexceptionalPrimitiveCharacters q Z).card *
        (Z : ℝ) ^ (-(8 : ℝ)) := by
  have hsum := Finset.sum_le_card_nsmul
    (taoUnexceptionalPrimitiveCharacters q Z)
    (fun χ : DirichletCharacter ℂ q =>
      ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (1000 : ℕ))
    ((Z : ℝ) ^ (-(8 : ℝ))) (fun χ hχ => by
      have hdata := mem_taoUnexceptionalPrimitiveCharacters.mp hχ
      exact (norm_taoNormalizedPrimeCharacterSum_pow_thousand_lt
        hdata.1 hdata.2.1 hdata.2.2).le)
  simpa only [nsmul_eq_mul, Nat.cast_ofNat] using hsum

/-- There are at most `φ(q)` unexceptional primitive characters, since this
is the cardinality of the complete character group modulo `q`. -/
theorem card_taoUnexceptionalPrimitiveCharacters_le_totient
    (q Z : ℕ) (hq : 0 < q) :
    (taoUnexceptionalPrimitiveCharacters q Z).card ≤ q.totient := by
  letI : NeZero q := ⟨hq.ne'⟩
  calc
    (taoUnexceptionalPrimitiveCharacters q Z).card ≤
        Fintype.card (DirichletCharacter ℂ q) := by
      rw [← Finset.card_univ]
      exact Finset.card_le_card fun χ _hχ => Finset.mem_univ χ
    _ = q.totient := by
      rw [← Nat.card_eq_fintype_card]
      exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q

/-- Totient-sized form of the source's trivial unexceptional contribution. -/
theorem sum_unexceptionalPrimeCharacter_pow_thousand_le_totient_mul
    (q Z : ℕ) (hq : 0 < q) :
    (∑ χ ∈ taoUnexceptionalPrimitiveCharacters q Z,
        ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (1000 : ℕ)) ≤
      (q.totient : ℝ) * (Z : ℝ) ^ (-(8 : ℝ)) := by
  calc
    (∑ χ ∈ taoUnexceptionalPrimitiveCharacters q Z,
        ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (1000 : ℕ)) ≤
        (taoUnexceptionalPrimitiveCharacters q Z).card *
          (Z : ℝ) ^ (-(8 : ℝ)) :=
      sum_unexceptionalPrimeCharacter_pow_thousand_le_card_mul q Z
    _ ≤ (q.totient : ℝ) * (Z : ℝ) ^ (-(8 : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg Z) _)
      exact_mod_cast card_taoUnexceptionalPrimitiveCharacters_le_totient q Z hq

/-- Exact algebraic interface from the Section 6 high moment to Lemma 5.1:
the primitive nonprincipal 1000th moment is bounded by the exceptional squared
moment plus the explicit unexceptional error `φ(q) Z^(-8)`. -/
theorem sum_primitiveNonprincipalPrimeCharacter_pow_thousand_le
    (q Z : ℕ) (hq : 0 < q) (hZ : (taoDyadicPrimeBand Z).Nonempty) :
    (∑ χ ∈ taoPrimitiveNonprincipalCharacters q,
        ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (1000 : ℕ)) ≤
      (∑ χ ∈ taoExceptionalPrimitiveCharacters q Z,
          ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (2 : ℕ)) +
        (q.totient : ℝ) * (Z : ℝ) ^ (-(8 : ℝ)) := by
  calc
    (∑ χ ∈ taoPrimitiveNonprincipalCharacters q,
        ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (1000 : ℕ)) =
        (∑ χ ∈ taoExceptionalPrimitiveCharacters q Z,
            ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (1000 : ℕ)) +
          ∑ χ ∈ taoUnexceptionalPrimitiveCharacters q Z,
            ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (1000 : ℕ) := by
      rw [taoPrimitiveNonprincipalCharacters_eq_exceptional_union_unexceptional,
        Finset.sum_union
          (taoExceptionalPrimitiveCharacters_disjoint_unexceptional q Z)]
    _ ≤ (∑ χ ∈ taoExceptionalPrimitiveCharacters q Z,
            ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (2 : ℕ)) +
          (q.totient : ℝ) * (Z : ℝ) ^ (-(8 : ℝ)) :=
      add_le_add
        (sum_exceptionalPrimeCharacter_pow_thousand_le_sum_sq q Z hZ)
        (sum_unexceptionalPrimeCharacter_pow_thousand_le_totient_mul q Z hq)

/-- A fixed conductor fiber is bounded by the exceptional squared moment at
that conductor plus the exact unexceptional error.  This is the direct
finite consumer interface for Lemma 5.1. -/
theorem taoFixedConductorPrimitiveMomentSum_le_exceptional_sq_add
    (q d Z : ℕ) [NeZero q] (hdPos : 0 < d) (hdOne : d ≠ 1)
    (hZ : (taoDyadicPrimeBand Z).Nonempty) :
    taoFixedConductorPrimitiveMomentSum q d Z ≤
      (∑ ψ ∈ taoExceptionalPrimitiveCharacters d Z,
          ‖taoNormalizedPrimeCharacterSum ψ Z‖ ^ (2 : ℕ)) +
        (d.totient : ℝ) * (Z : ℝ) ^ (-(8 : ℝ)) := by
  rw [taoFixedConductorPrimitiveMomentSum_eq_image]
  exact (sum_fixedConductorPrimitiveCharacter_pow_thousand_le q d Z hdOne).trans
    (sum_primitiveNonprincipalPrimeCharacter_pow_thousand_le
      d Z hdPos hZ)

/-- Complete elementary conductor reduction for an ambient character sum.
The principal character contributes one; every nonprincipal character is
placed injectively in its primitive conductor fiber; unexceptional terms give
the explicit totient error; and only the exceptional squared moments remain
for Lemma 5.1. -/
theorem sum_allPrimeCharacter_pow_thousand_le_one_add_conductorExceptional
    (q Z : ℕ) (hq : 0 < q) (hZ : (taoDyadicPrimeBand Z).Nonempty)
    (hcoprime : ∀ p ∈ taoDyadicPrimeBand Z, Nat.Coprime p q) :
    (∑ χ : DirichletCharacter ℂ q,
        ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (1000 : ℕ)) ≤
      1 + ∑ d ∈ q.divisors.erase 1,
        ((∑ ψ ∈ taoExceptionalPrimitiveCharacters d Z,
            ‖taoNormalizedPrimeCharacterSum ψ Z‖ ^ (2 : ℕ)) +
          (d.totient : ℝ) * (Z : ℝ) ^ (-(8 : ℝ))) := by
  letI : NeZero q := ⟨hq.ne'⟩
  calc
    (∑ χ : DirichletCharacter ℂ q,
        ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (1000 : ℕ)) =
        1 + ∑ χ ∈ taoNonprincipalCharacters q,
          ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ (1000 : ℕ) :=
      sum_allPrimeCharacter_pow_thousand_eq_one_add_nonprincipal
        q Z hZ hcoprime
    _ = 1 + ∑ d ∈ q.divisors.erase 1,
        taoFixedConductorPrimitiveMomentSum q d Z := by
      rw [sum_nonprincipalPrimeCharacter_pow_thousand_eq_sum_fixedConductors
        q Z hq hcoprime]
    _ ≤ 1 + ∑ d ∈ q.divisors.erase 1,
        ((∑ ψ ∈ taoExceptionalPrimitiveCharacters d Z,
            ‖taoNormalizedPrimeCharacterSum ψ Z‖ ^ (2 : ℕ)) +
          (d.totient : ℝ) * (Z : ℝ) ^ (-(8 : ℝ))) := by
      have hsum :
          (∑ d ∈ q.divisors.erase 1,
              taoFixedConductorPrimitiveMomentSum q d Z) ≤
            ∑ d ∈ q.divisors.erase 1,
              ((∑ ψ ∈ taoExceptionalPrimitiveCharacters d Z,
                  ‖taoNormalizedPrimeCharacterSum ψ Z‖ ^ (2 : ℕ)) +
                (d.totient : ℝ) * (Z : ℝ) ^ (-(8 : ℝ))) := by
        apply Finset.sum_le_sum
        intro d hd
        have hdMem : d ∈ q.divisors := Finset.mem_of_mem_erase hd
        have hdDvd : d ∣ q := (Nat.mem_divisors.mp hdMem).1
        have hdPos : 0 < d := Nat.pos_of_dvd_of_pos hdDvd hq
        exact taoFixedConductorPrimitiveMomentSum_le_exceptional_sq_add
          q d Z hdPos (Finset.ne_of_mem_erase hd) hZ
      simpa only [add_comm] using add_le_add_left hsum (1 : ℝ)

/-- Tuple-modulus specialization of the complete conductor reduction.  The
scale-separation hypothesis is exactly the source condition ensuring that
the primes averaged in `s_P` exceed every prime in the small tuple modulus. -/
theorem sum_taoSmallPrimeTupleCharacter_pow_thousand_le_conductorExceptional
    {x H P : ℕ} {t : Fin 50 → ℕ × ℕ}
    (ht : t ∈ Fintype.piFinset
      (fun _ : Fin 50 => taoSmallAntiSieveIndices x H))
    (hcutoff : taoSmallAntiSievePrimeCutoff x < P)
    (hP : (taoDyadicPrimeBand P).Nonempty) :
    (∑ χ : DirichletCharacter ℂ (taoSmallPrimeTupleModulus t),
        ‖taoNormalizedPrimeCharacterSum χ P‖ ^ (1000 : ℕ)) ≤
      1 + ∑ d ∈ (taoSmallPrimeTupleModulus t).divisors.erase 1,
        ((∑ ψ ∈ taoExceptionalPrimitiveCharacters d P,
            ‖taoNormalizedPrimeCharacterSum ψ P‖ ^ (2 : ℕ)) +
          (d.totient : ℝ) * (P : ℝ) ^ (-(8 : ℝ))) := by
  apply sum_allPrimeCharacter_pow_thousand_le_one_add_conductorExceptional
    (taoSmallPrimeTupleModulus t) P
    (taoSmallPrimeTupleModulus_pos_of_mem ht) hP
  intro p hp
  exact coprime_taoSmallPrimeTupleModulus_of_mem_dyadicBand
    ht hcutoff hp

/-- The conductor-reduced upper bound for one tail coordinate in the complete
ordered fiftieth-moment expansion. -/
def taoSmallPrimeConductorBoundAtCoordinate
    (P : Fin 1001 → ℕ) (x H : ℕ) (j : Fin 1001) : ℝ :=
  ∑ t ∈ Fintype.piFinset
      (fun _ : Fin 50 => taoSmallAntiSieveIndices x H),
    (∏ k, Real.log (t k).2) *
      (((2 ^ (50 : ℕ) : ℝ) / taoSmallPrimeTupleModulus t) *
        (1 + ∑ d ∈ (taoSmallPrimeTupleModulus t).divisors.erase 1,
          ((∑ ψ ∈ taoExceptionalPrimitiveCharacters d (P j),
              ‖taoNormalizedPrimeCharacterSum ψ (P j)‖ ^ (2 : ℕ)) +
            (d.totient : ℝ) * (P j : ℝ) ^ (-(8 : ℝ)))))

/-- Exact insertion of the primitive-conductor estimate into one coordinate
of the ordered fiftieth moment. -/
theorem taoSmallPrimeCharacterMomentAtCoordinate_le_conductorBound
    (P : Fin 1001 → ℕ) (x H : ℕ) (j : Fin 1001)
    (hcutoff : taoSmallAntiSievePrimeCutoff x < P j)
    (hPj : (taoDyadicPrimeBand (P j)).Nonempty) :
    taoSmallPrimeCharacterMomentAtCoordinate P x H j ≤
      taoSmallPrimeConductorBoundAtCoordinate P x H j := by
  unfold taoSmallPrimeCharacterMomentAtCoordinate
  unfold taoSmallPrimeConductorBoundAtCoordinate
  apply Finset.sum_le_sum
  intro t ht
  apply mul_le_mul_of_nonneg_left
  · apply mul_le_mul_of_nonneg_left
    · exact sum_taoSmallPrimeTupleCharacter_pow_thousand_le_conductorExceptional
        ht hcutoff hPj
    · positivity
  · apply Finset.prod_nonneg
    intro k _hk
    have hkPrime := (mem_taoSmallAntiSieveIndices.mp
      (Fintype.mem_piFinset.mp ht k)).2.2.1
    exact Real.log_nonneg (by exact_mod_cast hkPrime.one_le)

/-- The complete small-prime fiftieth moment is controlled, for one of the
literal 1000 tail coordinates, by the conductor-reduced tuple sum. -/
theorem exists_taoSmallPrimeFiftiethMoment_le_conductorBound
    (P : Fin 1001 → ℕ)
    (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (x H m' : ℕ)
    (hcutoff : ∀ j ∈ Finset.univ.erase (0 : Fin 1001),
      taoSmallAntiSievePrimeCutoff x < P j) :
    ∃ j ∈ Finset.univ.erase (0 : Fin 1001),
      taoSmallPrimeFiftiethMoment P hP x H m' ≤
        1000 * taoSmallPrimeConductorBoundAtCoordinate P x H j := by
  rcases exists_taoSmallPrimeFiftiethMoment_le_coordinateCharacterMoment
      P hP x H m' with ⟨j, hj, hMoment⟩
  refine ⟨j, hj, hMoment.trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (taoSmallPrimeCharacterMomentAtCoordinate_le_conductorBound
      P x H j (hcutoff j hj) (hP j)) (by norm_num)

end

end Tao2026
