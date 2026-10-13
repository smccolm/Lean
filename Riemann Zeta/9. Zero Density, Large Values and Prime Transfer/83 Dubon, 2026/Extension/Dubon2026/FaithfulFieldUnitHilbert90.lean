import Dubon2026.OriginalGroupCohomologyReindex
import Mathlib.FieldTheory.Fixed
import Mathlib.Algebra.Group.Action.Units
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90

/-! # Original unit cohomology for a finite faithful field action

The existing fixed-field Galois equivalence identifies the actual unit
action with the existing finite-extension Hilbert90 coefficient. Original
cohomology reindexing transfers its vanishing. This is the shorter route
to the original local-stabilizer H1 input in DUB-17's idele formula.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance] Units.mulDistribMulActionRight
variable (G F : Type) [Group G] [Finite G] [Field F]
  [MulSemiringAction G F] [FaithfulSMul G F]

/-- The actual unit action is the pullback of the original automorphism-unit action over its fixed field. -/
def faithfulFieldUnitCoefficientIso :
    Rep.res (FixedPoints.toAlgAutMulEquiv G F).toMonoidHom
        (Rep.ofAlgebraAutOnUnits (FixedPoints.subfield G F) F) ≅
      Rep.ofMulDistribMulAction G Fˣ :=
  Rep.mkIso {
    __ := LinearEquiv.refl ℤ (Additive Fˣ)
    isIntertwining' g := by
      apply LinearMap.ext
      intro x
      rfl }

/-- Original unit cohomology for the faithful action is the actual fixed-field extension cohomology. -/
def faithfulFieldUnitCohomologyIso (n : ℕ) :
    groupCohomology (Rep.ofAlgebraAutOnUnits (FixedPoints.subfield G F) F) n ≅
      groupCohomology (Rep.ofMulDistribMulAction G Fˣ) n :=
  originalCohomologyReindex _ (FixedPoints.toAlgAutMulEquiv G F) n ≪≫
    (groupCohomology.functor ℤ G n).mapIso (faithfulFieldUnitCoefficientIso G F)

/-- Existing Hilbert90 kills original unit H1 for every finite faithful field action. -/
theorem faithfulFieldUnit_first_cohomology_zero :
    Limits.IsZero (groupCohomology (Rep.ofMulDistribMulAction G Fˣ) 1) := by
  letI : Fintype G := Fintype.ofFinite G
  have hz : Limits.IsZero
      (groupCohomology (Rep.ofAlgebraAutOnUnits (FixedPoints.subfield G F) F) 1) :=
    ModuleCat.isZero_iff_subsingleton.mpr inferInstance
  exact Limits.IsZero.of_iso hz (faithfulFieldUnitCohomologyIso G F 1).symm

end
end Dubon2026
