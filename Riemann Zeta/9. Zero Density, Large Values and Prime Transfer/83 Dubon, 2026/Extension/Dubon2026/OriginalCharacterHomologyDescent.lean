import Dubon2026.OriginalCharacterChainEvaluation

/-! # Descent of original character evaluation to first homology

This is the low-degree pairing required on DUB-17's finite class/Ext
route. A cocycle defines a functional on the actual first homology,
and vanishing on all cycles is equivalent to being a coboundary.
Injectivity is used only for the extension of a linear functional.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {k G : Type} [CommRing k] [Group G]
variable (Q : Type) [AddCommGroup Q] [Module k Q] [Module.Injective k Q]
variable (M : Rep.{0} k G)

/-- A character cochain vanishes on original one-cycles exactly when it is a coboundary. -/
theorem originalCharacter_coboundary_iff_cycles_annihilation (c : G → M →ₗ[k] Q) :
    c ∈ groupCohomology.coboundaries₁ (originalLinearCharacterRep Q M) ↔
      ∀ z : groupHomology.cycles₁ M, originalCharacterChainEvaluation Q M c z.val = 0 := by
  constructor
  · rintro ⟨η, rfl⟩ z
    rw [originalCharacter_coboundary_evaluation]
    have hz : groupHomology.d₁₀ M z.val = 0 := z.property
    rw [hz, map_zero]
  · intro hc
    obtain ⟨η, hη⟩ := originalInjectiveCharacter_factor
      (groupHomology.d₁₀ M).hom (originalCharacterChainEvaluation Q M c)
      (fun z hz => hc ⟨z, hz⟩)
    refine ⟨η, ?_⟩
    funext g
    apply LinearMap.ext
    intro x
    have he := hη (Finsupp.single g x)
    change η (groupHomology.d₁₀ M (Finsupp.single g x)) = _ at he
    rw [groupHomology.d₁₀_single, map_sub, originalCharacterChainEvaluation_single] at he
    exact he

/-- Original character cocycle evaluation descends to the literal first homology group. -/
theorem originalCharacter_homology_descent_exists
    (c : groupCohomology.cocycles₁ (originalLinearCharacterRep Q M)) :
    ∃ χ : groupHomology M 1 →ₗ[k] Q, ∀ z : groupHomology.cycles₁ M,
      χ (groupHomology.H1π M z) = originalCharacterChainEvaluation Q M c.val z.val := by
  apply originalInjectiveCharacter_factor (groupHomology.H1π M).hom
    (originalCharacterChainEvaluation Q M c.val ∘ₗ (groupHomology.cycles₁ M).subtype)
  intro z hz
  obtain ⟨w, hw⟩ := (groupHomology.H1π_eq_zero_iff z).mp hz
  change originalCharacterChainEvaluation Q M c.val z.val = 0
  rw [← hw]
  exact (originalCharacter_cocycle_iff_boundary_annihilation Q M c.val).mp c.property w

/-- The functional on original first homology defined by a character cocycle. -/
def originalCharacterHomologyEvaluation
    (c : groupCohomology.cocycles₁ (originalLinearCharacterRep Q M)) :
    groupHomology M 1 →ₗ[k] Q :=
  Classical.choose (originalCharacter_homology_descent_exists Q M c)

/-- The descended functional evaluates representatives by the literal original chain sum. -/
theorem originalCharacterHomologyEvaluation_cycle
    (c : groupCohomology.cocycles₁ (originalLinearCharacterRep Q M))
    (z : groupHomology.cycles₁ M) :
    originalCharacterHomologyEvaluation Q M c (groupHomology.H1π M z) =
      originalCharacterChainEvaluation Q M c.val z.val :=
  Classical.choose_spec (originalCharacter_homology_descent_exists Q M c) z

/-- The descended functional is zero exactly when the original cocycle represents zero cohomology. -/
theorem originalCharacterHomologyEvaluation_eq_zero_iff
    (c : groupCohomology.cocycles₁ (originalLinearCharacterRep Q M)) :
    originalCharacterHomologyEvaluation Q M c = 0 ↔
      groupCohomology.H1π (originalLinearCharacterRep Q M) c = 0 := by
  constructor
  · intro h
    apply groupCohomology.H1π_eq_zero_iff c |>.mpr
    apply (originalCharacter_coboundary_iff_cycles_annihilation Q M c.val).mpr
    intro z
    rw [← originalCharacterHomologyEvaluation_cycle, h, LinearMap.zero_apply]
  · intro hc
    have h := (originalCharacter_coboundary_iff_cycles_annihilation Q M c.val).mp
      ((groupCohomology.H1π_eq_zero_iff c).mp hc)
    apply LinearMap.ext
    intro x
    induction x using groupHomology.H1_induction_on with
    | h z => exact (originalCharacterHomologyEvaluation_cycle Q M c z).trans (h z)

end
end Dubon2026
