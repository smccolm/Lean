import Tao2026.ExceptionalCharacterAbsorption

/-!
# Fixed-level exceptional characters as a Lemma 5.1 family

This module embeds the literal finite set of exceptional primitive characters
of one level into the heterogeneous family interface by taking `q₂ = 1`.
It proves exact preservation of cardinality and squared prime sums, then
transfers the Burgess-conditional self-improving Lemma 5.1 result to the
fixed-conductor sums consumed by the Section 6 character expansion.
-/

namespace Tao2026

open Filter

noncomputable def castDirichletCharacterLevel {m n : ℕ} (h : m = n)
    (χ : DirichletCharacter ℂ m) : DirichletCharacter ℂ n :=
  h ▸ χ

theorem castDirichletCharacterLevel_isPrimitive {m n : ℕ} (h : m = n)
    {χ : DirichletCharacter ℂ m} (hχ : DirichletCharacter.IsPrimitive χ) :
    DirichletCharacter.IsPrimitive (castDirichletCharacterLevel h χ) := by
  subst n
  exact hχ

theorem castDirichletCharacterLevel_injective {m n : ℕ} (h : m = n) :
    Function.Injective (@castDirichletCharacterLevel m n h) := by
  subst n
  exact Function.injective_id

theorem castDirichletCharacterLevel_apply_natCast {m n : ℕ} (h : m = n)
    (χ : DirichletCharacter ℂ m) (k : ℕ) :
    castDirichletCharacterLevel h χ (k : ZMod n) = χ (k : ZMod m) := by
  subst n
  rfl

/-- Two primitive Dirichlet characters whose lifts agree at the lcm have
equal original levels and are equal after transport across that equality. -/
theorem primitiveCharacter_eq_of_changeLevel_lcm_eq
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {χ : DirichletCharacter ℂ m} {ψ : DirichletCharacter ℂ n}
    (hχ : DirichletCharacter.IsPrimitive χ)
    (hψ : DirichletCharacter.IsPrimitive ψ)
    (heq :
      DirichletCharacter.changeLevel (Nat.dvd_lcm_left m n) χ =
        DirichletCharacter.changeLevel (Nat.dvd_lcm_right m n) ψ) :
    ∃ hmn : m = n, castDirichletCharacterLevel hmn χ = ψ := by
  letI : NeZero m := ⟨hm.ne'⟩
  letI : NeZero n := ⟨hn.ne'⟩
  have hprod :
      DirichletCharacter.changeLevel (m.dvd_mul_right n) χ =
        DirichletCharacter.changeLevel (n.dvd_mul_left m) ψ := by
    let hlcm : m.lcm n ∣ m * n := Nat.lcm_dvd_mul m n
    calc
      DirichletCharacter.changeLevel (m.dvd_mul_right n) χ =
          DirichletCharacter.changeLevel hlcm
            (DirichletCharacter.changeLevel (Nat.dvd_lcm_left m n) χ) := by
        rw [← DirichletCharacter.changeLevel_trans]
      _ = DirichletCharacter.changeLevel hlcm
            (DirichletCharacter.changeLevel (Nat.dvd_lcm_right m n) ψ) := by
        rw [heq]
      _ = DirichletCharacter.changeLevel (n.dvd_mul_left m) ψ := by
        rw [← DirichletCharacter.changeLevel_trans]
  have hχFactors : χ.FactorsThrough (m.gcd n) :=
    DirichletCharacter.factorsThrough_gcd (χ := χ) ψ hprod
  have hprodRev :
      DirichletCharacter.changeLevel (n.dvd_mul_right m) ψ =
        DirichletCharacter.changeLevel (m.dvd_mul_left n) χ := by
    let hlcmRev : m.lcm n ∣ n * m := by
      exact Nat.lcm_dvd (m.dvd_mul_left n) (n.dvd_mul_right m)
    calc
      DirichletCharacter.changeLevel (n.dvd_mul_right m) ψ =
          DirichletCharacter.changeLevel hlcmRev
            (DirichletCharacter.changeLevel (Nat.dvd_lcm_right m n) ψ) := by
        rw [← DirichletCharacter.changeLevel_trans]
      _ = DirichletCharacter.changeLevel hlcmRev
            (DirichletCharacter.changeLevel (Nat.dvd_lcm_left m n) χ) := by
        rw [heq]
      _ = DirichletCharacter.changeLevel (m.dvd_mul_left n) χ := by
        rw [← DirichletCharacter.changeLevel_trans]
  have hψFactors : ψ.FactorsThrough (n.gcd m) :=
    DirichletCharacter.factorsThrough_gcd (χ := ψ) χ hprodRev
  have hmnDvd : m ∣ n := by
    have hc : χ.conductor ∣ m.gcd n :=
      DirichletCharacter.conductor_dvd_of_mem_conductorSet χ hχFactors
    rw [hχ] at hc
    exact hc.trans (Nat.gcd_dvd_right m n)
  have hnmDvd : n ∣ m := by
    have hc : ψ.conductor ∣ n.gcd m :=
      DirichletCharacter.conductor_dvd_of_mem_conductorSet ψ hψFactors
    rw [hψ] at hc
    exact hc.trans (Nat.gcd_dvd_right n m)
  have hmn : m = n := Nat.dvd_antisymm hmnDvd hnmDvd
  subst n
  refine ⟨rfl, ?_⟩
  letI : NeZero (m.lcm m) :=
    ⟨Nat.lcm_ne_zero hm.ne' hm.ne'⟩
  exact (DirichletCharacter.changeLevel_injective
    (R := ℂ) (Nat.dvd_lcm_left m m)) heq

/-- Primitive datum records with positive common factor are determined by
their lifts to the pair lcm. -/
theorem TaoExceptionalCharacterDatum.eq_of_changeLevel_eq
    {q₁ Z : ℕ} (hq₁ : 0 < q₁)
    (a b : TaoExceptionalCharacterDatum q₁ Z)
    (heq :
      DirichletCharacter.changeLevel
          (Nat.dvd_lcm_left a.period b.period) a.χ =
        DirichletCharacter.changeLevel
          (Nat.dvd_lcm_right a.period b.period) b.χ) :
    a = b := by
  obtain ⟨hperiod, hchar⟩ :=
    primitiveCharacter_eq_of_changeLevel_lcm_eq
      (a.period_pos hq₁) (b.period_pos hq₁) a.χ_primitive b.χ_primitive heq
  have hq₂ : a.q₂ = b.q₂ := by
    unfold TaoExceptionalCharacterDatum.period at hperiod
    exact Nat.mul_left_cancel hq₁ hperiod
  have hcharHEq : HEq a.χ b.χ :=
    (eqRec_heq hperiod a.χ).symm.trans (heq_of_eq hchar)
  cases a with
  | mk aq₂ haq₂ hacop harange aχ haχ =>
    cases b with
    | mk bq₂ hbq₂ hbcop hbrange bχ hbχ =>
      dsimp only at hq₂ hcharHEq
      subst bq₂
      cases hcharHEq
      rfl

/-- Every finite family of primitive datum records is automatically
pairwise separated once its common factor is positive. -/
theorem isSeparatedTaoExceptionalFamily_of_commonFactor_pos
    {q₁ Z : ℕ} (hq₁ : 0 < q₁)
    (W : Finset (TaoExceptionalCharacterDatum q₁ Z)) :
    IsSeparatedTaoExceptionalFamily W := by
  intro a ha b hb hba heq
  exact hba (TaoExceptionalCharacterDatum.eq_of_changeLevel_eq hq₁ a b heq).symm

noncomputable def taoFixedLevelExceptionalDatumEmbedding
    (q Z : ℕ) (hq : Squarefree q)
    (hrange : (q : ℝ) ≤ (Z : ℝ) ^ taoBurgessPeriodExponent) :
    ↥(taoExceptionalPrimitiveCharacters q Z) ↪
      TaoExceptionalCharacterDatum q Z where
  toFun χ := {
    q₂ := 1
    q₂_squarefree := by simp
    q₁_coprime_q₂ := by simp
    q₂_le_sqrt := by
      norm_num only [Nat.cast_one]
      rw [Real.one_le_sqrt]
      apply (le_div_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hq.ne_zero)).2
      simpa using hrange
    χ := castDirichletCharacterLevel (Nat.mul_one q).symm χ.1
    χ_primitive := castDirichletCharacterLevel_isPrimitive _
      (mem_taoExceptionalPrimitiveCharacters.mp χ.2).1 }
  inj' := by
    intro χ ψ h
    letI : NeZero q := ⟨hq.ne_zero⟩
    apply Subtype.ext
    ext x
    have hv := congrArg (fun a : TaoExceptionalCharacterDatum q Z => a.value) h
    have hn := congrFun hv x.val.val
    change castDirichletCharacterLevel (Nat.mul_one q).symm χ.1
        (x.val.val : ZMod (q * 1)) =
      castDirichletCharacterLevel (Nat.mul_one q).symm ψ.1
        (x.val.val : ZMod (q * 1)) at hn
    rw [castDirichletCharacterLevel_apply_natCast,
      castDirichletCharacterLevel_apply_natCast] at hn
    simpa only [ZMod.natCast_zmod_val] using hn

noncomputable def taoFixedLevelExceptionalFamily
    (q Z : ℕ) (hq : Squarefree q)
    (hrange : (q : ℝ) ≤ (Z : ℝ) ^ taoBurgessPeriodExponent) :
    Finset (TaoExceptionalCharacterDatum q Z) :=
  (taoExceptionalPrimitiveCharacters q Z).attach.map
    (taoFixedLevelExceptionalDatumEmbedding q Z hq hrange)

theorem card_taoFixedLevelExceptionalFamily (q Z : ℕ) (hq : Squarefree q)
    (hrange : (q : ℝ) ≤ (Z : ℝ) ^ taoBurgessPeriodExponent) :
    (taoFixedLevelExceptionalFamily q Z hq hrange).card =
      (taoExceptionalPrimitiveCharacters q Z).card := by
  simp [taoFixedLevelExceptionalFamily]

theorem taoFixedLevelExceptionalFamily_isSeparated (q Z : ℕ) (hq : Squarefree q)
    (hrange : (q : ℝ) ≤ (Z : ℝ) ^ taoBurgessPeriodExponent) :
    IsSeparatedTaoExceptionalFamily
      (taoFixedLevelExceptionalFamily q Z hq hrange) := by
  intro a ha b hb hba
  change a ∈ (taoExceptionalPrimitiveCharacters q Z).attach.map
    (taoFixedLevelExceptionalDatumEmbedding q Z hq hrange) at ha
  change b ∈ (taoExceptionalPrimitiveCharacters q Z).attach.map
    (taoFixedLevelExceptionalDatumEmbedding q Z hq hrange) at hb
  rw [Finset.mem_map] at ha hb
  obtain ⟨χ, hχ, rfl⟩ := ha
  obtain ⟨ψ, hψ, rfl⟩ := hb
  intro heq
  apply hba
  have hqpos : 0 < q := Nat.pos_of_ne_zero hq.ne_zero
  letI : NeZero ((q * 1).lcm (q * 1)) :=
    ⟨Nat.ne_of_gt (Nat.lcm_pos (Nat.mul_pos hqpos one_pos)
      (Nat.mul_pos hqpos one_pos))⟩
  have heq' : DirichletCharacter.changeLevel
        (Nat.dvd_lcm_left (q * 1) (q * 1))
        (taoFixedLevelExceptionalDatumEmbedding q Z hq hrange χ).χ =
      DirichletCharacter.changeLevel
        (Nat.dvd_lcm_left (q * 1) (q * 1))
        (taoFixedLevelExceptionalDatumEmbedding q Z hq hrange ψ).χ := by
    simpa only [TaoExceptionalCharacterDatum.period,
      taoFixedLevelExceptionalDatumEmbedding] using heq
  have hcast := (DirichletCharacter.changeLevel_injective
    (R := ℂ) (Nat.dvd_lcm_left (q * 1) (q * 1))) heq'
  have hchar : χ.1 = ψ.1 :=
    castDirichletCharacterLevel_injective _ hcast
  have hsub : χ = ψ := Subtype.ext hchar
  rw [hsub]

theorem taoFixedLevelExceptionalFamily_isExceptional (q Z : ℕ) (hq : Squarefree q)
    (hrange : (q : ℝ) ≤ (Z : ℝ) ^ taoBurgessPeriodExponent) :
    ∀ a ∈ taoFixedLevelExceptionalFamily q Z hq hrange,
      taoExceptionalPrimeCharacterThreshold Z ≤
        ‖finiteNormalizedPrimeBandSum Z a.value‖ := by
  intro a ha
  change a ∈ (taoExceptionalPrimitiveCharacters q Z).attach.map
    (taoFixedLevelExceptionalDatumEmbedding q Z hq hrange) at ha
  rw [Finset.mem_map] at ha
  obtain ⟨χ, hχ, rfl⟩ := ha
  rw [show (taoFixedLevelExceptionalDatumEmbedding q Z hq hrange χ).value =
      fun n : ℕ => χ.1 (n : ZMod q) by
    funext n
    exact castDirichletCharacterLevel_apply_natCast _ χ.1 n]
  rw [finiteNormalizedPrimeBandSum_eq_taoNormalizedPrimeCharacterSum]
  exact (mem_taoExceptionalPrimitiveCharacters.mp χ.2).2.2

theorem sum_taoFixedLevelExceptionalFamily_sq (q Z : ℕ) (hq : Squarefree q)
    (hrange : (q : ℝ) ≤ (Z : ℝ) ^ taoBurgessPeriodExponent) :
    (∑ a ∈ taoFixedLevelExceptionalFamily q Z hq hrange,
      ‖finiteNormalizedPrimeBandSum Z a.value‖ ^ 2) =
    ∑ χ ∈ taoExceptionalPrimitiveCharacters q Z,
      ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ 2 := by
  classical
  unfold taoFixedLevelExceptionalFamily
  rw [Finset.sum_map]
  calc
    (∑ χ ∈ (taoExceptionalPrimitiveCharacters q Z).attach,
        ‖finiteNormalizedPrimeBandSum Z
          ((taoFixedLevelExceptionalDatumEmbedding q Z hq hrange) χ).value‖ ^ 2) =
      ∑ χ ∈ (taoExceptionalPrimitiveCharacters q Z).attach,
        ‖taoNormalizedPrimeCharacterSum χ.1 Z‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [show ((taoFixedLevelExceptionalDatumEmbedding q Z hq hrange) χ).value =
          fun n : ℕ => χ.1 (n : ZMod q) by
        funext n
        exact castDirichletCharacterLevel_apply_natCast _ χ.1 n]
      rw [finiteNormalizedPrimeBandSum_eq_taoNormalizedPrimeCharacterSum]
    _ = ∑ χ ∈ taoExceptionalPrimitiveCharacters q Z,
        ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ 2 :=
      by
        simpa using Finset.sum_attach
          (taoExceptionalPrimitiveCharacters q Z)
          (fun χ => ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ 2)

noncomputable def taoFixedLevelExceptionalFamilyAt (q Z : ℕ) :
    Finset (TaoExceptionalCharacterDatum q Z) :=
  if h : Squarefree q ∧
      (q : ℝ) ≤ (Z : ℝ) ^ taoBurgessPeriodExponent then
    taoFixedLevelExceptionalFamily q Z h.1 h.2
  else ∅

theorem taoFixedLevelExceptionalFamilyAt_eq (q Z : ℕ) (hq : Squarefree q)
    (hrange : (q : ℝ) ≤ (Z : ℝ) ^ taoBurgessPeriodExponent) :
    taoFixedLevelExceptionalFamilyAt q Z =
      taoFixedLevelExceptionalFamily q Z hq hrange := by
  unfold taoFixedLevelExceptionalFamilyAt
  rw [dif_pos (And.intro hq hrange)]

theorem card_taoFixedLevelExceptionalFamilyAt (q Z : ℕ) (hq : Squarefree q)
    (hrange : (q : ℝ) ≤ (Z : ℝ) ^ taoBurgessPeriodExponent) :
    (taoFixedLevelExceptionalFamilyAt q Z).card =
      (taoExceptionalPrimitiveCharacters q Z).card := by
  rw [taoFixedLevelExceptionalFamilyAt_eq q Z hq hrange]
  exact card_taoFixedLevelExceptionalFamily q Z hq hrange

theorem taoFixedLevelExceptionalFamilyAt_isSeparated (q Z : ℕ) (hq : Squarefree q)
    (hrange : (q : ℝ) ≤ (Z : ℝ) ^ taoBurgessPeriodExponent) :
    IsSeparatedTaoExceptionalFamily
      (taoFixedLevelExceptionalFamilyAt q Z) := by
  rw [taoFixedLevelExceptionalFamilyAt_eq q Z hq hrange]
  exact taoFixedLevelExceptionalFamily_isSeparated q Z hq hrange

theorem taoFixedLevelExceptionalFamilyAt_isExceptional (q Z : ℕ) (hq : Squarefree q)
    (hrange : (q : ℝ) ≤ (Z : ℝ) ^ taoBurgessPeriodExponent) :
    ∀ a ∈ taoFixedLevelExceptionalFamilyAt q Z,
      taoExceptionalPrimeCharacterThreshold Z ≤
        ‖finiteNormalizedPrimeBandSum Z a.value‖ := by
  rw [taoFixedLevelExceptionalFamilyAt_eq q Z hq hrange]
  exact taoFixedLevelExceptionalFamily_isExceptional q Z hq hrange

theorem sum_taoFixedLevelExceptionalFamilyAt_sq (q Z : ℕ) (hq : Squarefree q)
    (hrange : (q : ℝ) ≤ (Z : ℝ) ^ taoBurgessPeriodExponent) :
    (∑ a ∈ taoFixedLevelExceptionalFamilyAt q Z,
      ‖finiteNormalizedPrimeBandSum Z a.value‖ ^ 2) =
    ∑ χ ∈ taoExceptionalPrimitiveCharacters q Z,
      ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ 2 := by
  rw [taoFixedLevelExceptionalFamilyAt_eq q Z hq hrange]
  exact sum_taoFixedLevelExceptionalFamily_sq q Z hq hrange

theorem exists_eventually_fixedLevelExceptional_card_le_and_secondMoment_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    (q : ℕ → ℕ)
    (hq : ∀ᶠ Z : ℕ in atTop, Squarefree (q Z))
    (hrange : ∀ᶠ Z : ℕ in atTop,
      (q Z : ℝ) ≤ (Z : ℝ) ^ taoBurgessPeriodExponent) :
    ∃ K : ℝ, 0 < K ∧
      (∀ᶠ Z : ℕ in atTop,
        ((taoExceptionalPrimitiveCharacters (q Z) Z).card : ℝ) ≤
          K * (Z : ℝ) ^ (2 / 125 : ℝ)) ∧
      (∀ᶠ Z : ℕ in atTop,
        ∑ χ ∈ taoExceptionalPrimitiveCharacters (q Z) Z,
          ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ 2 ≤ K) := by
  let W : ∀ Z, Finset (TaoExceptionalCharacterDatum (q Z) Z) :=
    fun Z => taoFixedLevelExceptionalFamilyAt (q Z) Z
  have hsep : ∀ᶠ Z : ℕ in atTop,
      IsSeparatedTaoExceptionalFamily (W Z) := by
    filter_upwards [hq, hrange] with Z hqZ hrangeZ
    exact taoFixedLevelExceptionalFamilyAt_isSeparated (q Z) Z hqZ hrangeZ
  have hexceptional : ∀ᶠ Z : ℕ in atTop,
      ∀ a ∈ W Z, taoExceptionalPrimeCharacterThreshold Z ≤
        ‖finiteNormalizedPrimeBandSum Z a.value‖ := by
    filter_upwards [hq, hrange] with Z hqZ hrangeZ
    exact taoFixedLevelExceptionalFamilyAt_isExceptional (q Z) Z hqZ hrangeZ
  obtain ⟨K, hKpos, hcard, hmoment⟩ :=
    exists_eventually_exceptionalFamily_card_le_and_secondMoment_of_explicitBurgess
      hC hburgess q W hq hsep hexceptional
  refine ⟨K, hKpos, ?_, ?_⟩
  · filter_upwards [hcard, hq, hrange] with Z hcardZ hqZ hrangeZ
    rw [← card_taoFixedLevelExceptionalFamilyAt (q Z) Z hqZ hrangeZ]
    exact hcardZ
  · filter_upwards [hmoment, hq, hrange] with Z hmomentZ hqZ hrangeZ
    rw [← sum_taoFixedLevelExceptionalFamilyAt_sq (q Z) Z hqZ hrangeZ]
    exact hmomentZ

/-- Literal fixed-conductor form of every conclusion in Tao's Lemma 5.1,
including the more general `O(λ⁻²)` tail statement. -/
theorem exists_eventually_fixedLevelExceptional_card_secondMoment_and_tail_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    (q : ℕ → ℕ)
    (hq : ∀ᶠ Z : ℕ in atTop, Squarefree (q Z))
    (hrange : ∀ᶠ Z : ℕ in atTop,
      (q Z : ℝ) ≤ (Z : ℝ) ^ taoBurgessPeriodExponent) :
    ∃ K : ℝ, 0 < K ∧
      (∀ᶠ Z : ℕ in atTop,
        ((taoExceptionalPrimitiveCharacters (q Z) Z).card : ℝ) ≤
          K * (Z : ℝ) ^ (2 / 125 : ℝ)) ∧
      (∀ᶠ Z : ℕ in atTop,
        ∑ χ ∈ taoExceptionalPrimitiveCharacters (q Z) Z,
          ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ 2 ≤ K) ∧
      ∀ threshold : ℕ → ℝ, (∀ᶠ Z : ℕ in atTop, 0 < threshold Z) →
        ∀ᶠ Z : ℕ in atTop,
          (((taoExceptionalPrimitiveCharacters (q Z) Z).filter fun χ =>
              threshold Z ≤ ‖taoNormalizedPrimeCharacterSum χ Z‖).card : ℝ) ≤
            K * (threshold Z)⁻¹ ^ (2 : ℕ) := by
  classical
  obtain ⟨K, hKpos, hcard, hmoment⟩ :=
    exists_eventually_fixedLevelExceptional_card_le_and_secondMoment_of_explicitBurgess
      hC hburgess q hq hrange
  refine ⟨K, hKpos, hcard, hmoment, ?_⟩
  intro threshold hthreshold
  filter_upwards [hmoment, hthreshold] with Z hsum hthresholdZ
  exact card_norm_ge_le_of_sum_sq_le hthresholdZ hsum

end Tao2026
