import Dubon2026.OriginalIdeleClassTowerCoefficients
import Dubon2026.OriginalGroupChangeCohomologyIsomorphism
import Dubon2026.OriginalSecondCohomologyInflationRestriction

/-! # Faithful original idele-class H2 inflation between finite stages

The genuine field restriction and class inclusion induce the cohomology
map. Its injectivity follows from proved original kernel H1 vanishing,
with no vanishing premise. This preserves original finite-stage classes
when constructing the normalized global invariant required for DUB-17's
local sum formula and arithmetic duality.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
variable (K E L : Type) [Field K] [Field E] [NumberField E] [Field L] [NumberField L]
  [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
  [FiniteDimensional K L] [IsGalois K E] [IsGalois K L]

/-- The actual original class inclusion intertwines the restricted field action. -/
def originalIdeleClassTowerInclusion :
    Rep.res (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K))
      (originalIdeleClassRep K E) ⟶ originalIdeleClassRep K L :=
  Rep.ofHom {
    toLinearMap := (originalIdeleClassBaseChangeMap E L).toAdditive.toIntLinearMap
    isIntertwining' g := by
      apply LinearMap.ext
      intro x
      exact congrArg Additive.ofMul
        (originalIdeleClassBaseChangeMap_restrictNormal K E L g x.toMul).symm }

/-- Actual quotient inflation after the coefficient identification equals actual field-tower inflation. -/
theorem originalIdeleClassH2Inflation_composition :
    groupCohomology.map (galoisTowerQuotientEquiv K E L).toMonoidHom
        (originalIdeleClassTowerQuotientInclusion K E L) 2 ≫
      (originalSecondCohomologyInfRes (originalIdeleClassRep K L)
        (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K)).ker
        (originalIdeleClassTowerKernel_first_zero K E L)).f =
      groupCohomology.map (AlgEquiv.restrictNormalHom E)
        (originalIdeleClassTowerInclusion K E L) 2 := by
  change HomologicalComplex.homologyMap _ 2 ≫ HomologicalComplex.homologyMap _ 2 = _
  rw [← HomologicalComplex.homologyMap_comp]
  apply congrArg (fun t : groupCohomology.inhomogeneousCochains
      (originalIdeleClassRep K E) ⟶
      groupCohomology.inhomogeneousCochains (originalIdeleClassRep K L) =>
    HomologicalComplex.homologyMap t 2)
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext g
  rfl

/-- Actual original finite Galois class H2 inflation is injective. -/
theorem originalIdeleClassH2Inflation_injective :
    Function.Injective (groupCohomology.map (AlgEquiv.restrictNormalHom E)
      (originalIdeleClassTowerInclusion K E L) 2) := by
  let S := (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K)).ker
  let f := originalIdeleClassTowerQuotientInclusion K E L
  haveI : Mono f := (Rep.mono_iff_injective _).mpr
    (originalIdeleClassTowerQuotientInclusion_bijective K E L).1
  haveI : Epi f := (Rep.epi_iff_surjective _).mpr
    (originalIdeleClassTowerQuotientInclusion_bijective K E L).2
  haveI : IsIso f := isIso_of_mono_of_epi _
  let qmap := groupCohomology.map (galoisTowerQuotientEquiv K E L).toMonoidHom f 2
  haveI : IsIso qmap := originalGroupChangeCohomology_isIso
    (originalIdeleClassRep K E) ((originalIdeleClassRep K L).quotientToInvariants S)
    (galoisTowerQuotientEquiv K E L) f 2
  let X := originalSecondCohomologyInfRes (originalIdeleClassRep K L) S
    (originalIdeleClassTowerKernel_first_zero K E L)
  haveI : Mono X.f := originalSecondCohomology_inflation_mono (originalIdeleClassRep K L) S
    (originalIdeleClassTowerKernel_first_zero K E L)
  rw [← originalIdeleClassH2Inflation_composition K E L]
  exact ((ModuleCat.mono_iff_injective X.f).mp inferInstance).comp
    (asIso qmap).toLinearEquiv.injective

end
end Dubon2026
