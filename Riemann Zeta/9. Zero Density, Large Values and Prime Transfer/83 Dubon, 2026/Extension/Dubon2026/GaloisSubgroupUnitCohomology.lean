import Dubon2026.OriginalGroupCohomologyReindex
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90

/-! # Original subgroup unit cohomology is the actual fixed-field extension cohomology -/

namespace Dubon2026
noncomputable section

open CategoryTheory

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] (S : Subgroup Gal(L/K))

/-- The two original unit actions agree under the actual fixed-field
Galois correspondence, with the identity map on extension-field units. -/
def galoisSubgroupUnitCoefficientIso :
    Rep.res (IntermediateField.subgroupEquivAlgEquiv S).toMonoidHom
        (Rep.ofAlgebraAutOnUnits (IntermediateField.fixedField S) L) ≅
      Rep.res S.subtype (Rep.ofAlgebraAutOnUnits K L) :=
  Rep.mkIso {
    __ := LinearEquiv.refl ℤ (Additive Lˣ)
    isIntertwining' g := by
      ext x
      rfl }

/-- The original subgroup cohomology of extension-field units is
identified with the actual Galois cohomology over its literal fixed field. -/
def galoisSubgroupUnitCohomologyIso (n : ℕ) :
    groupCohomology (Rep.ofAlgebraAutOnUnits (IntermediateField.fixedField S) L) n ≅
      groupCohomology (Rep.res S.subtype (Rep.ofAlgebraAutOnUnits K L)) n :=
  originalCohomologyReindex _ (IntermediateField.subgroupEquivAlgEquiv S) n ≪≫
    (groupCohomology.functor ℤ S n).mapIso (galoisSubgroupUnitCoefficientIso S)

/-- Hilbert 90 for the actual fixed-field extension gives vanishing
first cohomology of the original subgroup action on the original units. -/
theorem galoisSubgroupUnit_first_cohomology_zero :
    Limits.IsZero (groupCohomology (Rep.res S.subtype (Rep.ofAlgebraAutOnUnits K L)) 1) := by
  have hzero : Limits.IsZero
      (groupCohomology (Rep.ofAlgebraAutOnUnits (IntermediateField.fixedField S) L) 1) :=
    ModuleCat.isZero_iff_subsingleton.mpr inferInstance
  exact Limits.IsZero.of_iso hzero (galoisSubgroupUnitCohomologyIso S 1).symm

/-- The actual subgroup H2 and the actual fixed-field extension H2 have
equal cardinalities, without an assumed norm index or local invariant. -/
theorem galoisSubgroupUnit_second_cohomology_card :
    Nat.card (groupCohomology (Rep.res S.subtype (Rep.ofAlgebraAutOnUnits K L)) 2) =
      Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits (IntermediateField.fixedField S) L) 2) :=
  (Nat.card_congr (galoisSubgroupUnitCohomologyIso S 2).toLinearEquiv.toEquiv).symm

end
end Dubon2026
