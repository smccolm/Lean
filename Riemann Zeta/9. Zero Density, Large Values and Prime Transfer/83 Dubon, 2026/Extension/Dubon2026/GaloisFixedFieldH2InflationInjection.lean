import Dubon2026.OriginalGroupChangeCohomologyIsomorphism
import Dubon2026.OriginalSecondCohomologyInflationRestriction
import Dubon2026.GaloisNormalInvariantUnitCoefficients
import Dubon2026.FiniteGaloisUnitTowerInflation

/-! # Injectivity of the original fixed-field Galois unit H2 inflation -/

namespace Dubon2026
noncomputable section

open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  (S : Subgroup Gal(L/K)) [S.Normal]

/-- Composing the actual fixed-field coefficient identification with
the original quotient inflation is exactly the genuine field-tower
inflation on the original cochains, hence on their original H2. -/
theorem galoisFixedFieldH2Inflation_composition :
    groupCohomology.map (IsGalois.normalAutEquivQuotient S).toMonoidHom
        (galoisNormalInvariantUnitInclusion S) 2 ≫
      (originalSecondCohomologyInfRes (Rep.ofAlgebraAutOnUnits K L) S
        (galoisSubgroupUnit_first_cohomology_zero S)).f =
    groupCohomology.map (AlgEquiv.restrictNormalHom (IntermediateField.fixedField S))
      (finiteGaloisUnitTowerInclusion K (IntermediateField.fixedField S) L) 2 := by
  change HomologicalComplex.homologyMap _ 2 ≫ HomologicalComplex.homologyMap _ 2 = _
  rw [← HomologicalComplex.homologyMap_comp]
  apply congrArg (fun t : groupCohomology.inhomogeneousCochains
      (Rep.ofAlgebraAutOnUnits K (IntermediateField.fixedField S)) ⟶
      groupCohomology.inhomogeneousCochains (Rep.ofAlgebraAutOnUnits K L) =>
    HomologicalComplex.homologyMap t 2)
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext g
  rfl

/-- The actual fixed-field inflation is injective. Hilbert 90 for the
original subgroup, not an assumed inflation theorem, supplies its input. -/
theorem galoisFixedFieldH2Inflation_mono :
    Mono (groupCohomology.map (AlgEquiv.restrictNormalHom (IntermediateField.fixedField S))
      (finiteGaloisUnitTowerInclusion K (IntermediateField.fixedField S) L) 2) := by
  haveI : Mono (galoisNormalInvariantUnitInclusion S) :=
    (Rep.mono_iff_injective _).mpr (galoisNormalInvariantUnitInclusion_bijective S).1
  haveI : Epi (galoisNormalInvariantUnitInclusion S) :=
    (Rep.epi_iff_surjective _).mpr (galoisNormalInvariantUnitInclusion_bijective S).2
  haveI : IsIso (galoisNormalInvariantUnitInclusion S) := isIso_of_mono_of_epi _
  haveI : IsIso (groupCohomology.map
      (IsGalois.normalAutEquivQuotient S).toMonoidHom (galoisNormalInvariantUnitInclusion S) 2) :=
    originalGroupChangeCohomology_isIso
    (Rep.ofAlgebraAutOnUnits K (IntermediateField.fixedField S))
    ((Rep.ofAlgebraAutOnUnits K L).quotientToInvariants S)
    (IsGalois.normalAutEquivQuotient S) (galoisNormalInvariantUnitInclusion S) 2
  haveI : Mono (originalSecondCohomologyInfRes (Rep.ofAlgebraAutOnUnits K L) S
      (galoisSubgroupUnit_first_cohomology_zero S)).f :=
    originalSecondCohomology_inflation_mono (Rep.ofAlgebraAutOnUnits K L) S
      (galoisSubgroupUnit_first_cohomology_zero S)
  rw [← galoisFixedFieldH2Inflation_composition S]
  apply (ModuleCat.mono_iff_injective _).mpr
  exact ((ModuleCat.mono_iff_injective
    (originalSecondCohomologyInfRes (Rep.ofAlgebraAutOnUnits K L) S
      (galoisSubgroupUnit_first_cohomology_zero S)).f).mp inferInstance).comp
    (asIso (groupCohomology.map (IsGalois.normalAutEquivQuotient S).toMonoidHom
      (galoisNormalInvariantUnitInclusion S) 2)).toLinearEquiv.injective

end
end Dubon2026
