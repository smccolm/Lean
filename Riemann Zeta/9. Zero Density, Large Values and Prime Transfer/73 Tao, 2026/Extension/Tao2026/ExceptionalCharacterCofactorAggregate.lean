import Tao2026.BadIntervalLargePrimeExceptional

/-!
# Exceptional characters with a common conductor factor

This module forms the precise heterogeneous family needed for Proposition 6.8.
For a fixed positive squarefree common factor `q₁`, it aggregates every
exceptional primitive character of conductor `q₁*q₂` as `q₂` ranges over a
finite admissible set.  The dependent embedding preserves the exact total
cardinality, automatic common-factor separation applies, and the
Burgess-conditional Lemma 5.1 gives an `O(Z^(2/125))` total character count.
-/

namespace Tao2026

open Filter
open scoped Classical Topology

noncomputable section

abbrev TaoCofactorExceptionalIndex (q₁ : ℕ) (D : Finset ℕ) (Z : ℕ) :=
  Σ q₂ : ↑D, ↑(taoExceptionalPrimitiveCharacters (q₁ * q₂.1) Z)

noncomputable def taoCofactorExceptionalDatumEmbedding
    (q₁ : ℕ) (D : Finset ℕ) (Z : ℕ) (hq₁pos : 0 < q₁)
    (hsq : ∀ q₂ ∈ D, Squarefree q₂)
    (hcop : ∀ q₂ ∈ D, Nat.Coprime q₁ q₂)
    (hrange : ∀ q₂ ∈ D, (q₂ : ℝ) ≤
      Real.sqrt ((Z : ℝ) ^ taoBurgessPeriodExponent / (q₁ : ℝ))) :
    TaoCofactorExceptionalIndex q₁ D Z ↪
      TaoExceptionalCharacterDatum q₁ Z where
  toFun a := {
    q₂ := a.1.1
    q₂_squarefree := hsq a.1.1 a.1.2
    q₁_coprime_q₂ := hcop a.1.1 a.1.2
    q₂_le_sqrt := hrange a.1.1 a.1.2
    χ := a.2.1
    χ_primitive := (mem_taoExceptionalPrimitiveCharacters.mp a.2.2).1 }
  inj' := by
    rintro ⟨aq, aχ⟩ ⟨bq, bχ⟩ hab
    have hqval : aq.1 = bq.1 :=
      congrArg TaoExceptionalCharacterDatum.q₂ hab
    have hq : aq = bq := Subtype.ext hqval
    subst bq
    letI : NeZero q₁ := ⟨Nat.ne_of_gt hq₁pos⟩
    letI : NeZero aq.1 := ⟨(hsq aq.1 aq.2).ne_zero⟩
    have hchars : aχ = bχ := by
      apply Subtype.ext
      ext x
      have hv := congrArg
        (fun c : TaoExceptionalCharacterDatum q₁ Z => c.value) hab
      have hn := congrFun hv x.val.val
      change aχ.1 (x.val.val : ZMod (q₁ * aq.1)) =
        bχ.1 (x.val.val : ZMod (q₁ * aq.1)) at hn
      have hx : (x.val.val : ZMod (q₁ * aq.1)) = x.val :=
        ZMod.natCast_zmod_val x.val
      simpa only [hx] using hn
    exact Sigma.ext rfl (heq_of_eq hchars)

noncomputable def taoCofactorExceptionalFamily
    (q₁ : ℕ) (D : Finset ℕ) (Z : ℕ) (hq₁pos : 0 < q₁)
    (hsq : ∀ q₂ ∈ D, Squarefree q₂)
    (hcop : ∀ q₂ ∈ D, Nat.Coprime q₁ q₂)
    (hrange : ∀ q₂ ∈ D, (q₂ : ℝ) ≤
      Real.sqrt ((Z : ℝ) ^ taoBurgessPeriodExponent / (q₁ : ℝ))) :
    Finset (TaoExceptionalCharacterDatum q₁ Z) :=
  Finset.univ.map
    (taoCofactorExceptionalDatumEmbedding q₁ D Z hq₁pos hsq hcop hrange)

theorem card_taoCofactorExceptionalFamily
    (q₁ : ℕ) (D : Finset ℕ) (Z : ℕ) (hq₁pos : 0 < q₁)
    (hsq : ∀ q₂ ∈ D, Squarefree q₂)
    (hcop : ∀ q₂ ∈ D, Nat.Coprime q₁ q₂)
    (hrange : ∀ q₂ ∈ D, (q₂ : ℝ) ≤
      Real.sqrt ((Z : ℝ) ^ taoBurgessPeriodExponent / (q₁ : ℝ))) :
    (taoCofactorExceptionalFamily q₁ D Z hq₁pos hsq hcop hrange).card =
      ∑ q₂ ∈ D, (taoExceptionalPrimitiveCharacters (q₁ * q₂) Z).card := by
  classical
  unfold taoCofactorExceptionalFamily
  rw [Finset.card_map, Finset.card_univ, Fintype.card_sigma]
  simpa only [Fintype.card_coe] using
    Finset.sum_attach D
      (fun q₂ => (taoExceptionalPrimitiveCharacters (q₁ * q₂) Z).card)

theorem sum_taoCofactorExceptionalFamily_sq
    (q₁ : ℕ) (D : Finset ℕ) (Z : ℕ) (hq₁pos : 0 < q₁)
    (hsq : ∀ q₂ ∈ D, Squarefree q₂)
    (hcop : ∀ q₂ ∈ D, Nat.Coprime q₁ q₂)
    (hrange : ∀ q₂ ∈ D, (q₂ : ℝ) ≤
      Real.sqrt ((Z : ℝ) ^ taoBurgessPeriodExponent / (q₁ : ℝ))) :
    (∑ a ∈ taoCofactorExceptionalFamily q₁ D Z hq₁pos hsq hcop hrange,
      ‖finiteNormalizedPrimeBandSum Z a.value‖ ^ 2) =
      ∑ q₂ ∈ D, ∑ χ ∈ taoExceptionalPrimitiveCharacters (q₁ * q₂) Z,
        ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ 2 := by
  classical
  unfold taoCofactorExceptionalFamily
  rw [Finset.sum_map]
  change (∑ i : TaoCofactorExceptionalIndex q₁ D Z,
      ‖finiteNormalizedPrimeBandSum Z
        ((taoCofactorExceptionalDatumEmbedding
          q₁ D Z hq₁pos hsq hcop hrange) i).value‖ ^ 2) = _
  rw [Fintype.sum_sigma]
  calc
    (∑ q₂ : ↑D, ∑ χ : ↑(taoExceptionalPrimitiveCharacters (q₁ * q₂.1) Z),
        ‖finiteNormalizedPrimeBandSum Z
          ((taoCofactorExceptionalDatumEmbedding
            q₁ D Z hq₁pos hsq hcop hrange) ⟨q₂, χ⟩).value‖ ^ 2) =
      ∑ q₂ : ↑D, ∑ χ : ↑(taoExceptionalPrimitiveCharacters (q₁ * q₂.1) Z),
        ‖taoNormalizedPrimeCharacterSum χ.1 Z‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro q₂ hq₂
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [show ((taoCofactorExceptionalDatumEmbedding
          q₁ D Z hq₁pos hsq hcop hrange) ⟨q₂, χ⟩).value =
          fun n : ℕ => χ.1 (n : ZMod (q₁ * q₂.1)) by rfl]
      rw [finiteNormalizedPrimeBandSum_eq_taoNormalizedPrimeCharacterSum]
    _ = ∑ q₂ ∈ D, ∑ χ ∈ taoExceptionalPrimitiveCharacters (q₁ * q₂) Z,
        ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ 2 := by
      change (∑ q₂ ∈ D.attach,
          ∑ χ ∈ (taoExceptionalPrimitiveCharacters (q₁ * q₂.1) Z).attach,
            ‖taoNormalizedPrimeCharacterSum χ.1 Z‖ ^ 2) = _
      calc
        (∑ q₂ ∈ D.attach,
            ∑ χ ∈ (taoExceptionalPrimitiveCharacters (q₁ * q₂.1) Z).attach,
              ‖taoNormalizedPrimeCharacterSum χ.1 Z‖ ^ 2) =
          ∑ q₂ ∈ D.attach,
            ∑ χ ∈ taoExceptionalPrimitiveCharacters (q₁ * q₂.1) Z,
              ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro q₂ hq₂
            simpa using Finset.sum_attach
              (taoExceptionalPrimitiveCharacters (q₁ * q₂.1) Z)
              (fun χ => ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ 2)
        _ = ∑ q₂ ∈ D,
            ∑ χ ∈ taoExceptionalPrimitiveCharacters (q₁ * q₂) Z,
              ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ 2 := by
            simpa using Finset.sum_attach D
              (fun q₂ => ∑ χ ∈
                taoExceptionalPrimitiveCharacters (q₁ * q₂) Z,
                  ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ 2)

theorem taoCofactorExceptionalFamily_isExceptional
    (q₁ : ℕ) (D : Finset ℕ) (Z : ℕ) (hq₁pos : 0 < q₁)
    (hsq : ∀ q₂ ∈ D, Squarefree q₂)
    (hcop : ∀ q₂ ∈ D, Nat.Coprime q₁ q₂)
    (hrange : ∀ q₂ ∈ D, (q₂ : ℝ) ≤
      Real.sqrt ((Z : ℝ) ^ taoBurgessPeriodExponent / (q₁ : ℝ))) :
    ∀ a ∈ taoCofactorExceptionalFamily q₁ D Z hq₁pos hsq hcop hrange,
      taoExceptionalPrimeCharacterThreshold Z ≤
        ‖finiteNormalizedPrimeBandSum Z a.value‖ := by
  classical
  intro a ha
  unfold taoCofactorExceptionalFamily at ha
  rw [Finset.mem_map] at ha
  obtain ⟨i, hi, rfl⟩ := ha
  rw [show (taoCofactorExceptionalDatumEmbedding q₁ D Z hq₁pos hsq hcop hrange i).value =
      fun n : ℕ => i.2.1 (n : ZMod (q₁ * i.1.1)) by rfl]
  rw [finiteNormalizedPrimeBandSum_eq_taoNormalizedPrimeCharacterSum]
  exact (mem_taoExceptionalPrimitiveCharacters.mp i.2.2).2.2

theorem exists_eventually_cofactorExceptional_card_le_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    (q₁ : ℕ → ℕ) (D : ℕ → Finset ℕ)
    (hq₁pos : ∀ᶠ Z : ℕ in atTop, 0 < q₁ Z)
    (hq₁sq : ∀ᶠ Z : ℕ in atTop, Squarefree (q₁ Z))
    (hDsq : ∀ᶠ Z : ℕ in atTop, ∀ q₂ ∈ D Z, Squarefree q₂)
    (hDcop : ∀ᶠ Z : ℕ in atTop, ∀ q₂ ∈ D Z, Nat.Coprime (q₁ Z) q₂)
    (hDrange : ∀ᶠ Z : ℕ in atTop, ∀ q₂ ∈ D Z, (q₂ : ℝ) ≤
      Real.sqrt ((Z : ℝ) ^ taoBurgessPeriodExponent / (q₁ Z : ℝ))) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ Z : ℕ in atTop,
      (((∑ q₂ ∈ D Z,
        (taoExceptionalPrimitiveCharacters (q₁ Z * q₂) Z).card : ℕ) : ℝ)) ≤
          K * (Z : ℝ) ^ (2 / 125 : ℝ) := by
  let W : ∀ Z, Finset (TaoExceptionalCharacterDatum (q₁ Z) Z) := fun Z =>
    if h : 0 < q₁ Z ∧
        (∀ q₂ ∈ D Z, Squarefree q₂) ∧
        (∀ q₂ ∈ D Z, Nat.Coprime (q₁ Z) q₂) ∧
        (∀ q₂ ∈ D Z, (q₂ : ℝ) ≤
          Real.sqrt ((Z : ℝ) ^ taoBurgessPeriodExponent / (q₁ Z : ℝ)))
    then taoCofactorExceptionalFamily (q₁ Z) (D Z) Z
      h.1 h.2.1 h.2.2.1 h.2.2.2
    else ∅
  have hsep : ∀ᶠ Z : ℕ in atTop,
      IsSeparatedTaoExceptionalFamily (W Z) := by
    filter_upwards [hq₁pos] with Z hZ
    exact isSeparatedTaoExceptionalFamily_of_commonFactor_pos hZ _
  have hexceptional : ∀ᶠ Z : ℕ in atTop,
      ∀ a ∈ W Z, taoExceptionalPrimeCharacterThreshold Z ≤
        ‖finiteNormalizedPrimeBandSum Z a.value‖ := by
    filter_upwards [hq₁pos, hDsq, hDcop, hDrange] with Z hpos hsq hcop hrange
    have hc : 0 < q₁ Z ∧
        (∀ q₂ ∈ D Z, Squarefree q₂) ∧
        (∀ q₂ ∈ D Z, Nat.Coprime (q₁ Z) q₂) ∧
        (∀ q₂ ∈ D Z, (q₂ : ℝ) ≤
          Real.sqrt ((Z : ℝ) ^ taoBurgessPeriodExponent / (q₁ Z : ℝ))) :=
      ⟨hpos, hsq, hcop, hrange⟩
    have hW : W Z = taoCofactorExceptionalFamily
        (q₁ Z) (D Z) Z hpos hsq hcop hrange := by
      dsimp only [W]
      rw [dif_pos hc]
    rw [hW]
    exact taoCofactorExceptionalFamily_isExceptional
      (q₁ Z) (D Z) Z hpos hsq hcop hrange
  obtain ⟨K, hK, hcard, hmoment⟩ :=
    exists_eventually_exceptionalFamily_card_le_and_secondMoment_of_explicitBurgess
      hC hburgess q₁ W hq₁sq hsep hexceptional
  refine ⟨K, hK, ?_⟩
  filter_upwards [hcard, hq₁pos, hDsq, hDcop, hDrange] with
      Z hcardZ hpos hsq hcop hrange
  have hc : 0 < q₁ Z ∧
      (∀ q₂ ∈ D Z, Squarefree q₂) ∧
      (∀ q₂ ∈ D Z, Nat.Coprime (q₁ Z) q₂) ∧
      (∀ q₂ ∈ D Z, (q₂ : ℝ) ≤
        Real.sqrt ((Z : ℝ) ^ taoBurgessPeriodExponent / (q₁ Z : ℝ))) :=
    ⟨hpos, hsq, hcop, hrange⟩
  have hW : W Z = taoCofactorExceptionalFamily
      (q₁ Z) (D Z) Z hpos hsq hcop hrange := by
    dsimp only [W]
    rw [dif_pos hc]
  rw [hW] at hcardZ
  rw [card_taoCofactorExceptionalFamily] at hcardZ
  exact hcardZ

/-- Varying cofactors that support at least one exceptional primitive
character after multiplication by the fixed common factor. -/
def taoExceptionalCofactorsIn (q₁ : ℕ) (D : Finset ℕ) (Z : ℕ) : Finset ℕ :=
  D.filter fun q₂ =>
    (taoExceptionalPrimitiveCharacters (q₁ * q₂) Z).Nonempty

theorem taoExceptionalCofactorsIn_subset (q₁ : ℕ) (D : Finset ℕ) (Z : ℕ) :
    taoExceptionalCofactorsIn q₁ D Z ⊆ D := by
  exact Finset.filter_subset _ _

theorem card_taoExceptionalCofactorsIn_le_sum_card
    (q₁ : ℕ) (D : Finset ℕ) (Z : ℕ) :
    (taoExceptionalCofactorsIn q₁ D Z).card ≤
      ∑ q₂ ∈ D,
        (taoExceptionalPrimitiveCharacters (q₁ * q₂) Z).card := by
  calc
    (taoExceptionalCofactorsIn q₁ D Z).card =
        ∑ q₂ ∈ taoExceptionalCofactorsIn q₁ D Z, 1 := by simp
    _ ≤ ∑ q₂ ∈ taoExceptionalCofactorsIn q₁ D Z,
        (taoExceptionalPrimitiveCharacters (q₁ * q₂) Z).card := by
      apply Finset.sum_le_sum
      intro q₂ hq₂
      exact Finset.one_le_card.mpr (Finset.mem_filter.mp hq₂).2
    _ ≤ ∑ q₂ ∈ D,
        (taoExceptionalPrimitiveCharacters (q₁ * q₂) Z).card := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (taoExceptionalCofactorsIn_subset q₁ D Z)
          (fun _ _ _ => Nat.zero_le _)

/-- Lemma 5.1 therefore bounds the number of exceptional varying cofactors
for every eventually admissible common-factor family. -/
theorem exists_eventually_card_taoExceptionalCofactorsIn_le_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    (q₁ : ℕ → ℕ) (D : ℕ → Finset ℕ)
    (hq₁pos : ∀ᶠ Z : ℕ in atTop, 0 < q₁ Z)
    (hq₁sq : ∀ᶠ Z : ℕ in atTop, Squarefree (q₁ Z))
    (hDsq : ∀ᶠ Z : ℕ in atTop, ∀ q₂ ∈ D Z, Squarefree q₂)
    (hDcop : ∀ᶠ Z : ℕ in atTop, ∀ q₂ ∈ D Z,
      Nat.Coprime (q₁ Z) q₂)
    (hDrange : ∀ᶠ Z : ℕ in atTop, ∀ q₂ ∈ D Z, (q₂ : ℝ) ≤
      Real.sqrt ((Z : ℝ) ^ taoBurgessPeriodExponent / (q₁ Z : ℝ))) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ Z : ℕ in atTop,
      ((taoExceptionalCofactorsIn (q₁ Z) (D Z) Z).card : ℝ) ≤
        K * (Z : ℝ) ^ (2 / 125 : ℝ) := by
  obtain ⟨K, hK, hcard⟩ :=
    exists_eventually_cofactorExceptional_card_le_of_explicitBurgess
      hC hburgess q₁ D hq₁pos hq₁sq hDsq hDcop hDrange
  refine ⟨K, hK, ?_⟩
  filter_upwards [hcard] with Z hZ
  calc
    ((taoExceptionalCofactorsIn (q₁ Z) (D Z) Z).card : ℝ) ≤
        (((∑ q₂ ∈ D Z,
          (taoExceptionalPrimitiveCharacters (q₁ Z * q₂) Z).card : ℕ) : ℝ)) := by
      exact_mod_cast card_taoExceptionalCofactorsIn_le_sum_card
        (q₁ Z) (D Z) Z
    _ ≤ K * (Z : ℝ) ^ (2 / 125 : ℝ) := hZ

end

end Tao2026
