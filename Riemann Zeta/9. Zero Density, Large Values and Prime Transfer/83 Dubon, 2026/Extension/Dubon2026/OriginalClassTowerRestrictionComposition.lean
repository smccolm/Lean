import Dubon2026.OriginalDegreeOneBaseClassRestriction

/-! Composition needed to preserve DUB-17's Sylow class when its fixed
field is lifted into the same arithmetic union. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
variable (K F E L : Type) [Field K] [Field F] [Field E] [Field L] [NumberField L]
  [Algebra K F] [Algebra K E] [Algebra K L] [Algebra F E] [Algebra F L] [Algebra E L]
  [IsScalarTower K F L] [IsScalarTower K E L] [IsScalarTower F E L]

/-- Actual class restriction composes along the same original field inclusions. -/
theorem originalIdeleClassTowerH2Restriction_comp
    (x : groupCohomology (originalIdeleClassRep K L) 2) :
    originalIdeleClassTowerH2Restriction F E L
      (originalIdeleClassTowerH2Restriction K F L x) =
      originalIdeleClassTowerH2Restriction K E L x := by
  induction x using groupCohomology.H2_induction_on with
  | h c =>
    change groupCohomology.map _ _ 2 (groupCohomology.map _ _ 2 (groupCohomology.H2π _ c)) =
      groupCohomology.map _ _ 2 (groupCohomology.H2π _ c)
    simp only [groupCohomology.H2π_comp_map_apply]
    apply congrArg (groupCohomology.H2π _)
    apply Subtype.ext
    funext g
    rfl

/-- A degree-one realization of the lower fixed field preserves the zero
locus of the original upper-field class restriction. -/
theorem originalIdeleClassTowerH2Restriction_zero_iff_degree_one
    (hd : Module.finrank F E = 1) (x : groupCohomology (originalIdeleClassRep K L) 2) :
    originalIdeleClassTowerH2Restriction K F L x = 0 ↔
      originalIdeleClassTowerH2Restriction K E L x = 0 := by
  haveI : IsIso (originalIdeleClassTowerH2Restriction F E L) :=
    originalIdeleClassTowerH2Restriction_isIso_of_degree_one F E L hd
  have hcomp := originalIdeleClassTowerH2Restriction_comp K F E L x
  constructor
  · intro h
    exact hcomp.symm.trans ((congrArg (originalIdeleClassTowerH2Restriction F E L) h).trans
      (map_zero (originalIdeleClassTowerH2Restriction F E L).hom))
  · intro h
    apply (asIso (originalIdeleClassTowerH2Restriction F E L)).toLinearEquiv.injective
    exact hcomp.trans (h.trans (map_zero (originalIdeleClassTowerH2Restriction F E L).hom).symm)

end
end Dubon2026
