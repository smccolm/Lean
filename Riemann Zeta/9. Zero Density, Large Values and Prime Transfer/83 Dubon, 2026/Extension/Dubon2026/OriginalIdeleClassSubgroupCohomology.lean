import Dubon2026.OriginalIdeleRestrictScalars
import Dubon2026.OriginalGroupCohomologyReindex

/-! # Original idele-class cohomology over actual fixed fields

The same original class group carries both actions. Reindexing by the
actual fixed-field Galois correspondence identifies them in every degree.
This is the subgroup comparison needed to extend the cyclic class-field
calculation to arbitrary finite Galois stages on DUB-17's global invariant
and arithmetic duality dependency chain.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
variable {K L : Type} [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] (S : Subgroup Gal(L/K))

/-- The fixed-field and subgroup actions on the original idele classes agree. -/
def originalIdeleClassSubgroupCoefficientIso :
    Rep.res (IntermediateField.subgroupEquivAlgEquiv S).toMonoidHom
        (originalIdeleClassRep (IntermediateField.fixedField S) L) ≅
      Rep.res S.subtype (originalIdeleClassRep K L) :=
  Rep.mkIso {
    __ := LinearEquiv.refl ℤ (Additive (OriginalNumberFieldIdeleClassGroup L))
    isIntertwining' g := by
      ext x
      rfl }

/-- Actual subgroup cohomology is the original fixed-field class cohomology. -/
def originalIdeleClassSubgroupCohomologyIso (n : ℕ) :
    groupCohomology (originalIdeleClassRep (IntermediateField.fixedField S) L) n ≅
      groupCohomology (Rep.res S.subtype (originalIdeleClassRep K L)) n :=
  originalCohomologyReindex _ (IntermediateField.subgroupEquivAlgEquiv S) n ≪≫
    (groupCohomology.functor ℤ S n).mapIso (originalIdeleClassSubgroupCoefficientIso S)

/-- Original subgroup H2 has the same order as the actual fixed-field class H2. -/
theorem originalIdeleClassSubgroup_second_card :
    Nat.card (groupCohomology (Rep.res S.subtype (originalIdeleClassRep K L)) 2) =
      Nat.card (groupCohomology (originalIdeleClassRep (IntermediateField.fixedField S) L) 2) :=
  (Nat.card_congr (originalIdeleClassSubgroupCohomologyIso S 2).toLinearEquiv.toEquiv).symm

end
end Dubon2026
