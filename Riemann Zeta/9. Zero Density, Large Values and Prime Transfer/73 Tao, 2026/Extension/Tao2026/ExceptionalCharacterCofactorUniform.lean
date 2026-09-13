import Tao2026.ExceptionalCharacterUniformCard

/-!
# Uniform exceptional counts for common-factor conductor families

This module applies the uniform cardinality form of Lemma 5.1 to the exact
dependent cofactor aggregate.  Selector diagonalization then gives the
quantifier order required in Proposition 6.8: one constant and one eventual
threshold work at the current scale for every positive squarefree common
factor and every admissible finite cofactor set.
-/

namespace Tao2026

open Filter
open scoped Classical Topology

noncomputable section

theorem exists_uniform_eventually_cofactorExceptional_card_le_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀) :
    ∃ A : ℝ, 0 < A ∧
      ∀ (q₁ : ℕ → ℕ) (D : ℕ → Finset ℕ),
        (∀ᶠ Z : ℕ in atTop, 0 < q₁ Z) →
        (∀ᶠ Z : ℕ in atTop, Squarefree (q₁ Z)) →
        (∀ᶠ Z : ℕ in atTop, ∀ q₂ ∈ D Z, Squarefree q₂) →
        (∀ᶠ Z : ℕ in atTop, ∀ q₂ ∈ D Z,
          Nat.Coprime (q₁ Z) q₂) →
        (∀ᶠ Z : ℕ in atTop, ∀ q₂ ∈ D Z, (q₂ : ℝ) ≤
          Real.sqrt ((Z : ℝ) ^ taoBurgessPeriodExponent / (q₁ Z : ℝ))) →
        ∀ᶠ Z : ℕ in atTop,
          (((∑ q₂ ∈ D Z,
            (taoExceptionalPrimitiveCharacters (q₁ Z * q₂) Z).card : ℕ) : ℝ)) ≤
              A * (Z : ℝ) ^ (2 / 125 : ℝ) := by
  obtain ⟨A, hA, huniform⟩ :=
    exists_uniform_eventually_exceptionalFamily_card_le_of_explicitBurgess
      hC hburgess
  refine ⟨A, hA, ?_⟩
  intro q₁ D hq₁pos hq₁sq hDsq hDcop hDrange
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
    filter_upwards [hq₁pos, hDsq, hDcop, hDrange] with
      Z hpos hsq hcop hrange
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
  have hcard := huniform q₁ W hq₁sq hsep hexceptional
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
  rw [hW, card_taoCofactorExceptionalFamily] at hcardZ
  exact hcardZ

/-- One constant works eventually pointwise for every admissible common
factor/cofactor-set pair at the current scale. -/
theorem exists_uniform_eventually_card_taoExceptionalCofactorsIn_le_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ Z : ℕ in atTop,
      ∀ q₁ : ℕ, ∀ D : Finset ℕ,
        0 < q₁ → Squarefree q₁ →
        (∀ q₂ ∈ D, Squarefree q₂) →
        (∀ q₂ ∈ D, Nat.Coprime q₁ q₂) →
        (∀ q₂ ∈ D, (q₂ : ℝ) ≤
          Real.sqrt ((Z : ℝ) ^ taoBurgessPeriodExponent / (q₁ : ℝ))) →
        ((taoExceptionalCofactorsIn q₁ D Z).card : ℝ) ≤
          A * (Z : ℝ) ^ (2 / 125 : ℝ) := by
  obtain ⟨A, hA, huniform⟩ :=
    exists_uniform_eventually_cofactorExceptional_card_le_of_explicitBurgess
      hC hburgess
  refine ⟨A, hA, ?_⟩
  let R : ℕ → (ℕ × Finset ℕ) → Prop := fun Z a =>
    0 < a.1 ∧ Squarefree a.1 ∧
      (∀ q₂ ∈ a.2, Squarefree q₂) ∧
      (∀ q₂ ∈ a.2, Nat.Coprime a.1 q₂) ∧
      (∀ q₂ ∈ a.2, (q₂ : ℝ) ≤
        Real.sqrt ((Z : ℝ) ^ taoBurgessPeriodExponent / (a.1 : ℝ)))
  let Q : ℕ → (ℕ × Finset ℕ) → Prop := fun Z a =>
    ((taoExceptionalCofactorsIn a.1 a.2 Z).card : ℝ) ≤
      A * (Z : ℝ) ^ (2 / 125 : ℝ)
  have hne : ∀ᶠ Z : ℕ in atTop, ∃ a, R Z a := by
    filter_upwards [] with Z
    refine ⟨(1, ∅), ?_⟩
    simp [R]
  have hselector : ∀ f : ℕ → (ℕ × Finset ℕ),
      (∀ᶠ Z : ℕ in atTop, R Z (f Z)) →
        ∀ᶠ Z : ℕ in atTop, Q Z (f Z) := by
    intro f hf
    have hpos : ∀ᶠ Z : ℕ in atTop, 0 < (f Z).1 := by
      filter_upwards [hf] with Z hZ
      exact hZ.1
    have hsq : ∀ᶠ Z : ℕ in atTop, Squarefree (f Z).1 := by
      filter_upwards [hf] with Z hZ
      exact hZ.2.1
    have hDsq : ∀ᶠ Z : ℕ in atTop, ∀ q₂ ∈ (f Z).2, Squarefree q₂ := by
      filter_upwards [hf] with Z hZ
      exact hZ.2.2.1
    have hDcop : ∀ᶠ Z : ℕ in atTop, ∀ q₂ ∈ (f Z).2,
        Nat.Coprime (f Z).1 q₂ := by
      filter_upwards [hf] with Z hZ
      exact hZ.2.2.2.1
    have hDrange : ∀ᶠ Z : ℕ in atTop, ∀ q₂ ∈ (f Z).2,
        (q₂ : ℝ) ≤ Real.sqrt
          ((Z : ℝ) ^ taoBurgessPeriodExponent / ((f Z).1 : ℝ)) := by
      filter_upwards [hf] with Z hZ
      exact hZ.2.2.2.2
    have hsum := huniform (fun Z => (f Z).1) (fun Z => (f Z).2)
      hpos hsq hDsq hDcop hDrange
    filter_upwards [hsum] with Z hZ
    dsimp only [Q]
    calc
      ((taoExceptionalCofactorsIn (f Z).1 (f Z).2 Z).card : ℝ) ≤
          (((∑ q₂ ∈ (f Z).2,
            (taoExceptionalPrimitiveCharacters ((f Z).1 * q₂) Z).card : ℕ) : ℝ)) := by
        exact_mod_cast card_taoExceptionalCofactorsIn_le_sum_card
          (f Z).1 (f Z).2 Z
      _ ≤ A * (Z : ℝ) ^ (2 / 125 : ℝ) := hZ
  have hall := eventually_forall_of_forall_selector hne hselector
  filter_upwards [hall] with Z hZ q₁ D hpos hsq hDsq hDcop hDrange
  exact hZ (q₁, D) ⟨hpos, hsq, hDsq, hDcop, hDrange⟩

/-- One absolute squared-moment constant works for every admissible
common-factor/cofactor family. -/
theorem exists_uniform_eventually_cofactorExceptional_secondMoment_le_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀) :
    ∃ M : ℝ, 0 < M ∧
      ∀ (q₁ : ℕ → ℕ) (D : ℕ → Finset ℕ),
        (∀ᶠ Z : ℕ in atTop, 0 < q₁ Z) →
        (∀ᶠ Z : ℕ in atTop, Squarefree (q₁ Z)) →
        (∀ᶠ Z : ℕ in atTop, ∀ q₂ ∈ D Z, Squarefree q₂) →
        (∀ᶠ Z : ℕ in atTop, ∀ q₂ ∈ D Z,
          Nat.Coprime (q₁ Z) q₂) →
        (∀ᶠ Z : ℕ in atTop, ∀ q₂ ∈ D Z, (q₂ : ℝ) ≤
          Real.sqrt ((Z : ℝ) ^ taoBurgessPeriodExponent / (q₁ Z : ℝ))) →
        ∀ᶠ Z : ℕ in atTop,
          ∑ q₂ ∈ D Z,
            ∑ χ ∈ taoExceptionalPrimitiveCharacters (q₁ Z * q₂) Z,
              ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ 2 ≤ M := by
  obtain ⟨M, hM, huniformMoment⟩ :=
    exists_uniform_eventually_exceptionalFamily_secondMoment_le_of_explicitBurgess
      hC hburgess
  refine ⟨M, hM, ?_⟩
  intro q₁ D hq₁pos hq₁sq hDsq hDcop hDrange
  obtain ⟨A, hA, hcard⟩ :=
    exists_eventually_cofactorExceptional_card_le_of_explicitBurgess
      hC hburgess q₁ D hq₁pos hq₁sq hDsq hDcop hDrange
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
  have hWcard : ∀ᶠ Z : ℕ in atTop,
      ((W Z).card : ℝ) ≤ A * (Z : ℝ) ^ (2 / 125 : ℝ) := by
    filter_upwards [hcard, hq₁pos, hDsq, hDcop, hDrange] with
      Z hcardZ hpos hsq hcop hrange
    have hc : 0 < q₁ Z ∧
        (∀ q₂ ∈ D Z, Squarefree q₂) ∧
        (∀ q₂ ∈ D Z, Nat.Coprime (q₁ Z) q₂) ∧
        (∀ q₂ ∈ D Z, (q₂ : ℝ) ≤
          Real.sqrt ((Z : ℝ) ^ taoBurgessPeriodExponent / (q₁ Z : ℝ))) :=
      ⟨hpos, hsq, hcop, hrange⟩
    rw [show W Z = taoCofactorExceptionalFamily
        (q₁ Z) (D Z) Z hpos hsq hcop hrange by
      dsimp only [W]
      rw [dif_pos hc]]
    rw [card_taoCofactorExceptionalFamily]
    exact hcardZ
  have hmoment := huniformMoment q₁ W hq₁sq hsep hWcard
  filter_upwards [hmoment, hq₁pos, hDsq, hDcop, hDrange] with
    Z hmomentZ hpos hsq hcop hrange
  have hc : 0 < q₁ Z ∧
      (∀ q₂ ∈ D Z, Squarefree q₂) ∧
      (∀ q₂ ∈ D Z, Nat.Coprime (q₁ Z) q₂) ∧
      (∀ q₂ ∈ D Z, (q₂ : ℝ) ≤
        Real.sqrt ((Z : ℝ) ^ taoBurgessPeriodExponent / (q₁ Z : ℝ))) :=
    ⟨hpos, hsq, hcop, hrange⟩
  rw [show W Z = taoCofactorExceptionalFamily
      (q₁ Z) (D Z) Z hpos hsq hcop hrange by
    dsimp only [W]
    rw [dif_pos hc]] at hmomentZ
  rw [sum_taoCofactorExceptionalFamily_sq] at hmomentZ
  exact hmomentZ

/-- Pointwise-uniform form of the common-factor exceptional squared moment.
The eventual cutoff is independent of the current common factor and cofactor
set. -/
theorem exists_uniform_eventually_cofactorExceptional_secondMoment_pointwise_le_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ Z : ℕ in atTop,
      ∀ q₁ : ℕ, ∀ D : Finset ℕ,
        0 < q₁ → Squarefree q₁ →
        (∀ q₂ ∈ D, Squarefree q₂) →
        (∀ q₂ ∈ D, Nat.Coprime q₁ q₂) →
        (∀ q₂ ∈ D, (q₂ : ℝ) ≤
          Real.sqrt ((Z : ℝ) ^ taoBurgessPeriodExponent / (q₁ : ℝ))) →
        ∑ q₂ ∈ D,
          ∑ χ ∈ taoExceptionalPrimitiveCharacters (q₁ * q₂) Z,
            ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ 2 ≤ M := by
  obtain ⟨M, hM, huniform⟩ :=
    exists_uniform_eventually_cofactorExceptional_secondMoment_le_of_explicitBurgess
      hC hburgess
  refine ⟨M, hM, ?_⟩
  let R : ℕ → (ℕ × Finset ℕ) → Prop := fun Z a =>
    0 < a.1 ∧ Squarefree a.1 ∧
      (∀ q₂ ∈ a.2, Squarefree q₂) ∧
      (∀ q₂ ∈ a.2, Nat.Coprime a.1 q₂) ∧
      (∀ q₂ ∈ a.2, (q₂ : ℝ) ≤
        Real.sqrt ((Z : ℝ) ^ taoBurgessPeriodExponent / (a.1 : ℝ)))
  let Q : ℕ → (ℕ × Finset ℕ) → Prop := fun Z a =>
    ∑ q₂ ∈ a.2,
      ∑ χ ∈ taoExceptionalPrimitiveCharacters (a.1 * q₂) Z,
        ‖taoNormalizedPrimeCharacterSum χ Z‖ ^ 2 ≤ M
  have hne : ∀ᶠ Z : ℕ in atTop, ∃ a, R Z a := by
    filter_upwards [] with Z
    refine ⟨(1, ∅), ?_⟩
    simp [R]
  have hselector : ∀ f : ℕ → (ℕ × Finset ℕ),
      (∀ᶠ Z : ℕ in atTop, R Z (f Z)) →
        ∀ᶠ Z : ℕ in atTop, Q Z (f Z) := by
    intro f hf
    have hpos : ∀ᶠ Z : ℕ in atTop, 0 < (f Z).1 := by
      filter_upwards [hf] with Z hZ
      exact hZ.1
    have hsq : ∀ᶠ Z : ℕ in atTop, Squarefree (f Z).1 := by
      filter_upwards [hf] with Z hZ
      exact hZ.2.1
    have hDsq : ∀ᶠ Z : ℕ in atTop, ∀ q₂ ∈ (f Z).2,
        Squarefree q₂ := by
      filter_upwards [hf] with Z hZ
      exact hZ.2.2.1
    have hDcop : ∀ᶠ Z : ℕ in atTop, ∀ q₂ ∈ (f Z).2,
        Nat.Coprime (f Z).1 q₂ := by
      filter_upwards [hf] with Z hZ
      exact hZ.2.2.2.1
    have hDrange : ∀ᶠ Z : ℕ in atTop, ∀ q₂ ∈ (f Z).2,
        (q₂ : ℝ) ≤ Real.sqrt
          ((Z : ℝ) ^ taoBurgessPeriodExponent / ((f Z).1 : ℝ)) := by
      filter_upwards [hf] with Z hZ
      exact hZ.2.2.2.2
    have hsum := huniform (fun Z => (f Z).1) (fun Z => (f Z).2)
      hpos hsq hDsq hDcop hDrange
    filter_upwards [hsum] with Z hZ
    exact hZ
  have hall := eventually_forall_of_forall_selector hne hselector
  filter_upwards [hall] with Z hZ q₁ D hpos hsq hDsq hDcop hDrange
  exact hZ (q₁, D) ⟨hpos, hsq, hDsq, hDcop, hDrange⟩

end

end Tao2026
