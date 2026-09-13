import Tao2026.ExceptionalCharacterFixedLevel

/-!
# Exceptional primitive characters across a finite conductor set

This module forms one heterogeneous Lemma 5.1 family from all literal
exceptional primitive characters whose conductors lie in a finite set.  The
dependent sigma index retains each character's true level.  Primitive
cross-level uniqueness proves separation, while cardinality and the squared
normalized-prime sum are preserved exactly.
-/

namespace Tao2026

open Filter

abbrev TaoConductorExceptionalIndex (D : Finset ℕ) (Z : ℕ) :=
  Σ q : ↑D, ↑(taoExceptionalPrimitiveCharacters q.1 Z)

noncomputable def taoConductorExceptionalDatumEmbedding
    (D : Finset ℕ) (Z : ℕ)
    (hsq : ∀ q ∈ D, Squarefree q)
    (hrange : ∀ q ∈ D,
      (q : ℝ) ≤ Real.sqrt ((Z : ℝ) ^ taoBurgessPeriodExponent)) :
    TaoConductorExceptionalIndex D Z ↪ TaoExceptionalCharacterDatum 1 Z where
  toFun a := {
    q₂ := a.1.1
    q₂_squarefree := hsq a.1.1 a.1.2
    q₁_coprime_q₂ := by simp
    q₂_le_sqrt := by simpa using hrange a.1.1 a.1.2
    χ := castDirichletCharacterLevel (Nat.one_mul a.1.1).symm a.2.1
    χ_primitive := castDirichletCharacterLevel_isPrimitive _
      (mem_taoExceptionalPrimitiveCharacters.mp a.2.2).1 }
  inj' := by
    rintro ⟨aq, aχ⟩ ⟨bq, bχ⟩ hab
    have hqval : aq.1 = bq.1 :=
      congrArg TaoExceptionalCharacterDatum.q₂ hab
    have hq : aq = bq := Subtype.ext hqval
    subst bq
    letI : NeZero aq.1 := ⟨(hsq aq.1 aq.2).ne_zero⟩
    have hchars : aχ = bχ := by
      apply Subtype.ext
      ext x
      have hv := congrArg
        (fun c : TaoExceptionalCharacterDatum 1 Z => c.value) hab
      have hn := congrFun hv x.val.val
      change castDirichletCharacterLevel (Nat.one_mul aq.1).symm aχ.1
          (x.val.val : ZMod (1 * aq.1)) =
        castDirichletCharacterLevel (Nat.one_mul aq.1).symm bχ.1
          (x.val.val : ZMod (1 * aq.1)) at hn
      rw [castDirichletCharacterLevel_apply_natCast,
        castDirichletCharacterLevel_apply_natCast] at hn
      convert hn using 1 <;> simp only [ZMod.natCast_zmod_val]
    exact Sigma.ext rfl (heq_of_eq hchars)

noncomputable def taoConductorExceptionalFamily
    (D : Finset ℕ) (Z : ℕ)
    (hsq : ∀ q ∈ D, Squarefree q)
    (hrange : ∀ q ∈ D,
      (q : ℝ) ≤ Real.sqrt ((Z : ℝ) ^ taoBurgessPeriodExponent)) :
    Finset (TaoExceptionalCharacterDatum 1 Z) :=
  Finset.univ.map (taoConductorExceptionalDatumEmbedding D Z hsq hrange)

theorem card_taoConductorExceptionalFamily
    (D : Finset ℕ) (Z : ℕ)
    (hsq : ∀ q ∈ D, Squarefree q)
    (hrange : ∀ q ∈ D,
      (q : ℝ) ≤ Real.sqrt ((Z : ℝ) ^ taoBurgessPeriodExponent)) :
    (taoConductorExceptionalFamily D Z hsq hrange).card =
      ∑ q ∈ D, (taoExceptionalPrimitiveCharacters q Z).card := by
  classical
  unfold taoConductorExceptionalFamily
  rw [Finset.card_map, Finset.card_univ, Fintype.card_sigma]
  simpa only [Fintype.card_coe] using
    Finset.sum_attach D
      (fun q => (taoExceptionalPrimitiveCharacters q Z).card)

theorem taoConductorExceptionalFamily_isSeparated
    (D : Finset ℕ) (Z : ℕ)
    (hsq : ∀ q ∈ D, Squarefree q)
    (hrange : ∀ q ∈ D,
      (q : ℝ) ≤ Real.sqrt ((Z : ℝ) ^ taoBurgessPeriodExponent)) :
    IsSeparatedTaoExceptionalFamily
      (taoConductorExceptionalFamily D Z hsq hrange) :=
  isSeparatedTaoExceptionalFamily_of_commonFactor_pos one_pos _

theorem taoConductorExceptionalFamily_isExceptional
    (D : Finset ℕ) (Z : ℕ)
    (hsq : ∀ q ∈ D, Squarefree q)
    (hrange : ∀ q ∈ D,
      (q : ℝ) ≤ Real.sqrt ((Z : ℝ) ^ taoBurgessPeriodExponent)) :
    ∀ a ∈ taoConductorExceptionalFamily D Z hsq hrange,
      taoExceptionalPrimeCharacterThreshold Z ≤
        ‖finiteNormalizedPrimeBandSum Z a.value‖ := by
  classical
  intro a ha
  unfold taoConductorExceptionalFamily at ha
  rw [Finset.mem_map] at ha
  obtain ⟨i, hi, rfl⟩ := ha
  rw [show (taoConductorExceptionalDatumEmbedding D Z hsq hrange i).value =
      fun n : ℕ => i.2.1 (n : ZMod i.1.1) by
    funext n
    exact castDirichletCharacterLevel_apply_natCast _ i.2.1 n]
  rw [finiteNormalizedPrimeBandSum_eq_taoNormalizedPrimeCharacterSum]
  exact (mem_taoExceptionalPrimitiveCharacters.mp i.2.2).2.2

theorem sum_taoConductorExceptionalFamily_sq
    (D : Finset ℕ) (Z : ℕ)
    (hsq : ∀ q ∈ D, Squarefree q)
    (hrange : ∀ q ∈ D,
      (q : ℝ) ≤ Real.sqrt ((Z : ℝ) ^ taoBurgessPeriodExponent)) :
    (∑ a ∈ taoConductorExceptionalFamily D Z hsq hrange,
      ‖finiteNormalizedPrimeBandSum Z a.value‖ ^ 2) =
    ∑ q ∈ D, ∑ χ ∈ taoExceptionalPrimitiveCharacters q Z,
      ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ 2 := by
  classical
  unfold taoConductorExceptionalFamily
  rw [Finset.sum_map]
  change (∑ i : TaoConductorExceptionalIndex D Z,
      ‖finiteNormalizedPrimeBandSum Z
        ((taoConductorExceptionalDatumEmbedding D Z hsq hrange) i).value‖ ^ 2) = _
  rw [Fintype.sum_sigma]
  calc
    (∑ q : ↑D, ∑ χ : ↑(taoExceptionalPrimitiveCharacters q.1 Z),
        ‖finiteNormalizedPrimeBandSum Z
          ((taoConductorExceptionalDatumEmbedding D Z hsq hrange) ⟨q, χ⟩).value‖ ^ 2) =
      ∑ q : ↑D, ∑ χ : ↑(taoExceptionalPrimitiveCharacters q.1 Z),
        ‖taoNormalizedPrimeCharacterSum χ.1 Z‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [show ((taoConductorExceptionalDatumEmbedding D Z hsq hrange) ⟨q, χ⟩).value =
          fun n : ℕ => χ.1 (n : ZMod q.1) by
        funext n
        exact castDirichletCharacterLevel_apply_natCast _ χ.1 n]
      rw [finiteNormalizedPrimeBandSum_eq_taoNormalizedPrimeCharacterSum]
    _ = ∑ q ∈ D, ∑ χ ∈ taoExceptionalPrimitiveCharacters q Z,
        ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ 2 := by
      change (∑ q ∈ D.attach,
          ∑ χ ∈ (taoExceptionalPrimitiveCharacters q.1 Z).attach,
            ‖taoNormalizedPrimeCharacterSum χ.1 Z‖ ^ 2) = _
      calc
        (∑ q ∈ D.attach,
            ∑ χ ∈ (taoExceptionalPrimitiveCharacters q.1 Z).attach,
              ‖taoNormalizedPrimeCharacterSum χ.1 Z‖ ^ 2) =
          ∑ q ∈ D.attach,
            ∑ χ ∈ taoExceptionalPrimitiveCharacters q.1 Z,
              ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro q hq
            simpa using Finset.sum_attach
              (taoExceptionalPrimitiveCharacters q.1 Z)
              (fun χ => ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ 2)
        _ = ∑ q ∈ D, ∑ χ ∈ taoExceptionalPrimitiveCharacters q Z,
              ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ 2 := by
            simpa using Finset.sum_attach D
              (fun q => ∑ χ ∈ taoExceptionalPrimitiveCharacters q Z,
                ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ 2)

def IsAdmissibleTaoExceptionalConductorSet (D : Finset ℕ) (Z : ℕ) : Prop :=
  (∀ q ∈ D, Squarefree q) ∧
    ∀ q ∈ D,
      (q : ℝ) ≤ Real.sqrt ((Z : ℝ) ^ taoBurgessPeriodExponent)

/-- The finite maximal set of squarefree conductors satisfying the exact
Burgess range at scale `Z`. -/
noncomputable def taoAllAdmissibleExceptionalConductors (Z : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.floor
    (Real.sqrt ((Z : ℝ) ^ taoBurgessPeriodExponent)))).filter Squarefree

theorem isAdmissible_taoAllAdmissibleExceptionalConductors (Z : ℕ) :
    IsAdmissibleTaoExceptionalConductorSet
      (taoAllAdmissibleExceptionalConductors Z) Z := by
  constructor
  · intro q hq
    exact (Finset.mem_filter.mp hq).2
  · intro q hq
    have hupper := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).2
    calc
      (q : ℝ) ≤ (Nat.floor
          (Real.sqrt ((Z : ℝ) ^ taoBurgessPeriodExponent)) : ℕ) := by
        exact_mod_cast hupper
      _ ≤ Real.sqrt ((Z : ℝ) ^ taoBurgessPeriodExponent) :=
        Nat.floor_le (Real.sqrt_nonneg _)

theorem subset_taoAllAdmissibleExceptionalConductors
    {D : Finset ℕ} {Z : ℕ}
    (hD : IsAdmissibleTaoExceptionalConductorSet D Z) :
    D ⊆ taoAllAdmissibleExceptionalConductors Z := by
  intro q hq
  rw [taoAllAdmissibleExceptionalConductors,
    Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨?_, Nat.le_floor (hD.2 q hq)⟩, hD.1 q hq⟩
  exact (hD.1 q hq).ne_zero.bot_lt

noncomputable def taoConductorExceptionalFamilyAt
    (D : Finset ℕ) (Z : ℕ) :
    Finset (TaoExceptionalCharacterDatum 1 Z) := by
  classical
  exact if h : IsAdmissibleTaoExceptionalConductorSet D Z then
    taoConductorExceptionalFamily D Z h.1 h.2
  else ∅

theorem taoConductorExceptionalFamilyAt_eq
    (D : Finset ℕ) (Z : ℕ)
    (h : IsAdmissibleTaoExceptionalConductorSet D Z) :
    taoConductorExceptionalFamilyAt D Z =
      taoConductorExceptionalFamily D Z h.1 h.2 := by
  classical
  unfold taoConductorExceptionalFamilyAt
  rw [dif_pos h]

theorem card_taoConductorExceptionalFamilyAt
    (D : Finset ℕ) (Z : ℕ)
    (h : IsAdmissibleTaoExceptionalConductorSet D Z) :
    (taoConductorExceptionalFamilyAt D Z).card =
      ∑ q ∈ D, (taoExceptionalPrimitiveCharacters q Z).card := by
  rw [taoConductorExceptionalFamilyAt_eq D Z h]
  exact card_taoConductorExceptionalFamily D Z h.1 h.2

theorem taoConductorExceptionalFamilyAt_isSeparated
    (D : Finset ℕ) (Z : ℕ)
    (h : IsAdmissibleTaoExceptionalConductorSet D Z) :
    IsSeparatedTaoExceptionalFamily
      (taoConductorExceptionalFamilyAt D Z) := by
  rw [taoConductorExceptionalFamilyAt_eq D Z h]
  exact taoConductorExceptionalFamily_isSeparated D Z h.1 h.2

theorem taoConductorExceptionalFamilyAt_isExceptional
    (D : Finset ℕ) (Z : ℕ)
    (h : IsAdmissibleTaoExceptionalConductorSet D Z) :
    ∀ a ∈ taoConductorExceptionalFamilyAt D Z,
      taoExceptionalPrimeCharacterThreshold Z ≤
        ‖finiteNormalizedPrimeBandSum Z a.value‖ := by
  rw [taoConductorExceptionalFamilyAt_eq D Z h]
  exact taoConductorExceptionalFamily_isExceptional D Z h.1 h.2

theorem sum_taoConductorExceptionalFamilyAt_sq
    (D : Finset ℕ) (Z : ℕ)
    (h : IsAdmissibleTaoExceptionalConductorSet D Z) :
    (∑ a ∈ taoConductorExceptionalFamilyAt D Z,
      ‖finiteNormalizedPrimeBandSum Z a.value‖ ^ 2) =
    ∑ q ∈ D, ∑ χ ∈ taoExceptionalPrimitiveCharacters q Z,
      ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ 2 := by
  rw [taoConductorExceptionalFamilyAt_eq D Z h]
  exact sum_taoConductorExceptionalFamily_sq D Z h.1 h.2

/-- A single Lemma 5.1 application controls the union of the exceptional
primitive characters over any eventually admissible finite set of
conductors.  In particular, the constant is uniform in both the conductor
set and its cardinality. -/
theorem exists_eventually_conductorExceptional_card_le_and_secondMoment_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    (D : ℕ → Finset ℕ)
    (hD : ∀ᶠ Z : ℕ in atTop,
      IsAdmissibleTaoExceptionalConductorSet (D Z) Z) :
    ∃ K : ℝ, 0 < K ∧
      (∀ᶠ Z : ℕ in atTop,
        ((∑ q ∈ D Z,
          (taoExceptionalPrimitiveCharacters q Z).card : ℕ) : ℝ) ≤
            K * (Z : ℝ) ^ (2 / 125 : ℝ)) ∧
      (∀ᶠ Z : ℕ in atTop,
        ∑ q ∈ D Z, ∑ χ ∈ taoExceptionalPrimitiveCharacters q Z,
          ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ 2 ≤ K) := by
  let q₁ : ℕ → ℕ := fun _ => 1
  let W : ∀ Z, Finset (TaoExceptionalCharacterDatum (q₁ Z) Z) :=
    fun Z => taoConductorExceptionalFamilyAt (D Z) Z
  have hq₁ : ∀ᶠ Z : ℕ in atTop, Squarefree (q₁ Z) := by
    filter_upwards [] with Z
    simp [q₁]
  have hsep : ∀ᶠ Z : ℕ in atTop,
      IsSeparatedTaoExceptionalFamily (W Z) := by
    filter_upwards [hD] with Z hDZ
    exact taoConductorExceptionalFamilyAt_isSeparated (D Z) Z hDZ
  have hexceptional : ∀ᶠ Z : ℕ in atTop,
      ∀ a ∈ W Z, taoExceptionalPrimeCharacterThreshold Z ≤
        ‖finiteNormalizedPrimeBandSum Z a.value‖ := by
    filter_upwards [hD] with Z hDZ
    exact taoConductorExceptionalFamilyAt_isExceptional (D Z) Z hDZ
  obtain ⟨K, hKpos, hcard, hmoment⟩ :=
    exists_eventually_exceptionalFamily_card_le_and_secondMoment_of_explicitBurgess
      hC hburgess q₁ W hq₁ hsep hexceptional
  refine ⟨K, hKpos, ?_, ?_⟩
  · filter_upwards [hcard, hD] with Z hcardZ hDZ
    rw [← card_taoConductorExceptionalFamilyAt (D Z) Z hDZ]
    exact hcardZ
  · filter_upwards [hmoment, hD] with Z hmomentZ hDZ
    rw [← sum_taoConductorExceptionalFamilyAt_sq (D Z) Z hDZ]
    exact hmomentZ

/-- One absolute eventual moment constant works simultaneously for every
finite admissible conductor set at the current scale.  This follows by
applying the aggregate theorem once to the maximal admissible conductor set
and using nonnegativity to pass to arbitrary subsets. -/
theorem exists_uniform_eventually_conductorExceptional_secondMoment_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ Z : ℕ in atTop,
      ∀ D : Finset ℕ, IsAdmissibleTaoExceptionalConductorSet D Z →
        ∑ q ∈ D, ∑ χ ∈ taoExceptionalPrimitiveCharacters q Z,
          ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ 2 ≤ K := by
  obtain ⟨K, hK, hcard, hmoment⟩ :=
    exists_eventually_conductorExceptional_card_le_and_secondMoment_of_explicitBurgess
      hC hburgess taoAllAdmissibleExceptionalConductors
        (Filter.Eventually.of_forall
          isAdmissible_taoAllAdmissibleExceptionalConductors)
  refine ⟨K, hK, ?_⟩
  filter_upwards [hmoment] with Z hZ D hD
  have hnonneg : ∀ q ∈ taoAllAdmissibleExceptionalConductors Z, q ∉ D →
      (0 : ℝ) ≤ ∑ χ ∈ taoExceptionalPrimitiveCharacters q Z,
        ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ 2 := by
    intro q hq hnot
    positivity
  exact (Finset.sum_le_sum_of_subset_of_nonneg
    (subset_taoAllAdmissibleExceptionalConductors hD) hnonneg).trans hZ

end Tao2026
