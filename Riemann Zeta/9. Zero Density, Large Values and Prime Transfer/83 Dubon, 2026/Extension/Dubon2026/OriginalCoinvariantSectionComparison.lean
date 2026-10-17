import Dubon2026.OriginalCoinducedLinearLift

/-! # Actual coinduced comparison from a coinvariant section

The original linear section extends by the already proved coinduced
trace. Literal point functions identify the induced coinvariant map as
bijective. This builds the concrete comparison needed for DUB-17's
mod-p projectivity argument; the section is a narrower linear input.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {G : Type} [Group G] [Fintype G] (A : Rep.{0} ℤ G)

/-- The original coinvariant module with trivial action, before actual coinduction. -/
abbrev originalCoinvariantTrivialRep : Rep ℤ G := Rep.trivial ℤ G A.ρ.Coinvariants

/-- The actual coinduced trace comparison extending a linear section of original coinvariants. -/
def originalCoinvariantSectionComparison (T : A.ρ.Coinvariants →ₗ[ℤ] A) :
    originalCoinducedFunctionRep (originalCoinvariantTrivialRep A) ⟶ A :=
  originalCoinducedLinearLift (originalCoinvariantTrivialRep A) A T

/-- The actual comparison constructed from a coinvariant section is surjective on original coinvariants. -/
theorem originalCoinvariantSectionComparison_coinvariant_surjective
    (T : A.ρ.Coinvariants →ₗ[ℤ] A)
    (hT : ∀ c, Representation.Coinvariants.mk A.ρ (T c) = c) :
    Function.Surjective (Representation.Coinvariants.map
      (originalCoinducedFunctionRep (originalCoinvariantTrivialRep A)).ρ A.ρ
      (originalCoinvariantSectionComparison A T).hom) := by
  intro c
  refine ⟨Representation.Coinvariants.mk _ (originalCoinducedPoint (originalCoinvariantTrivialRep A) c), ?_⟩
  rw [Representation.Coinvariants.map_mk]
  change Representation.Coinvariants.mk A.ρ
    ((originalCoinducedLinearLift (originalCoinvariantTrivialRep A) A T).hom _) = c
  rw [originalCoinducedLinearLift_point, hT]

/-- The actual comparison constructed from a coinvariant section is injective on original coinvariants. -/
theorem originalCoinvariantSectionComparison_coinvariant_injective
    (T : A.ρ.Coinvariants →ₗ[ℤ] A)
    (hT : ∀ c, Representation.Coinvariants.mk A.ρ (T c) = c) :
    Function.Injective (Representation.Coinvariants.map
      (originalCoinducedFunctionRep (originalCoinvariantTrivialRep A)).ρ A.ρ
      (originalCoinvariantSectionComparison A T).hom) := by
  intro a b hab
  obtain ⟨x, rfl⟩ := Representation.Coinvariants.mk_surjective _ a
  obtain ⟨y, rfl⟩ := Representation.Coinvariants.mk_surjective _ b
  rw [originalCoinduced_coinvariant_point_sum (originalCoinvariantTrivialRep A) x,
    originalCoinduced_coinvariant_point_sum (originalCoinvariantTrivialRep A) y] at hab ⊢
  rw [Representation.Coinvariants.map_mk, Representation.Coinvariants.map_mk] at hab
  change Representation.Coinvariants.mk A.ρ
      ((originalCoinducedLinearLift (originalCoinvariantTrivialRep A) A T).hom _) =
    Representation.Coinvariants.mk A.ρ
      ((originalCoinducedLinearLift (originalCoinvariantTrivialRep A) A T).hom _) at hab
  rw [originalCoinducedLinearLift_point, originalCoinducedLinearLift_point, hT, hT] at hab
  rw [hab]

end
end Dubon2026
