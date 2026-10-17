import Dubon2026.OriginalFiniteRelationAcyclicity

/-! # The genuine relation-module obstruction to extension

Use the actual connecting isomorphism and coefficient map. Extension
through the free cover kills this obstruction by the original exact
sequence. Its converse for the normalized arithmetic class coefficient
is still the required finite class/Ext duality theorem on DUB-17's route.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory

variable {G : Type} [Group G] (B C : Rep ℤ G)

/-- The original H1-to-H2 obstruction associated with the actual relation coefficient morphism. -/
def originalRelationExtensionObstruction (φ : originalRelationModule B ⟶ C) :
    groupCohomology B 1 ⟶ groupCohomology C 2 :=
  groupCohomology.δ (originalRelationShortComplex_shortExact B) 1 2 rfl ≫
    (groupCohomology.functor ℤ G 2).map φ

/-- Extending through the actual free cover annihilates the original connecting obstruction. -/
theorem originalRelationExtensionObstruction_zero_of_extension
    (φ : originalRelationModule B ⟶ C) (χ : Rep.free ℤ G B ⟶ C)
    (hχ : originalRelationInclusion B ≫ χ = φ) :
    originalRelationExtensionObstruction B C φ = 0 := by
  have hz : groupCohomology.δ (originalRelationShortComplex_shortExact B) 1 2 rfl ≫
      (groupCohomology.functor ℤ G 2).map (originalRelationInclusion B) = 0 :=
    (groupCohomology.mapShortComplex₁ (originalRelationShortComplex_shortExact B)
      (i := 1) (j := 2) rfl).zero
  unfold originalRelationExtensionObstruction
  rw [← hχ]
  erw [Functor.map_comp, ← Category.assoc, hz, Limits.zero_comp]

variable [Finite G] [Finite B]

/-- For the original finite coefficient, every relation H2 class is reached by the genuine connecting map, so vanishing of the obstruction is exactly vanishing of the relation cohomology map. -/
theorem originalRelationExtensionObstruction_zero_iff
    (φ : originalRelationModule B ⟶ C) :
    originalRelationExtensionObstruction B C φ = 0 ↔
      (groupCohomology.functor ℤ G 2).map φ = 0 := by
  haveI := originalRelationConnecting_isIso B
  unfold originalRelationExtensionObstruction
  constructor
  · intro h
    apply (cancel_epi (groupCohomology.δ (originalRelationShortComplex_shortExact B) 1 2 rfl)).1
    simpa only [Limits.comp_zero] using h
  · intro h
    erw [h, Limits.comp_zero]

end
end Dubon2026
