import Dubon2026.OriginalIdeleClassTowerCoefficients
import Dubon2026.GaloisUnitTowerRestriction

/-! # Original class H2 restriction along actual fixed-field enlargement

The coefficient group is unchanged and the group map is the actual
inclusion of field automorphisms. Its comparison with the restriction
kernel is literal on cochains. This supplies the other map in the exact
finite-stage class H2 sequence used for the global invariant and DUB-17's
local sum formula.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
variable (K E L : Type) [Field K] [Field E] [Field L] [NumberField L]
  [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]

/-- The actual subgroup restriction uses the identity on original upper-field classes. -/
def originalIdeleClassTowerRestrictionCoefficient :
    Rep.res (galoisTowerBaseRestriction K E L) (originalIdeleClassRep K L) ≅
      originalIdeleClassRep E L :=
  Rep.mkIso {
    __ := LinearEquiv.refl ℤ (Additive (OriginalNumberFieldIdeleClassGroup L))
    isIntertwining' g := by ext x; rfl }

/-- Actual original class H2 restriction along the inclusion of field automorphisms. -/
def originalIdeleClassTowerH2Restriction :
    groupCohomology (originalIdeleClassRep K L) 2 ⟶
      groupCohomology (originalIdeleClassRep E L) 2 :=
  groupCohomology.map (galoisTowerBaseRestriction K E L)
    (originalIdeleClassTowerRestrictionCoefficient K E L).hom 2

/-- Original field-tower restriction equals the kernel restriction after its actual Galois identification. -/
theorem originalIdeleClassTowerH2Restriction_kernel_composition [IsGalois K E] :
    originalIdeleClassTowerH2Restriction K E L ≫
      groupCohomology.map (galoisTowerKernelEquiv K E L).toMonoidHom
        (originalIdeleClassTowerKernelCoefficientIso K E L).hom 2 =
      groupCohomology.map (A := originalIdeleClassRep K L)
        (B := Rep.res (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K)).ker.subtype
          (originalIdeleClassRep K L))
        (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K)).ker.subtype (𝟙 _) 2 := by
  change HomologicalComplex.homologyMap _ 2 ≫ HomologicalComplex.homologyMap _ 2 = _
  rw [← HomologicalComplex.homologyMap_comp]
  apply congrArg (fun t : groupCohomology.inhomogeneousCochains (originalIdeleClassRep K L) ⟶
    groupCohomology.inhomogeneousCochains
      (Rep.res (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K)).ker.subtype
        (originalIdeleClassRep K L)) => HomologicalComplex.homologyMap t 2)
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext g
  rfl

end
end Dubon2026
