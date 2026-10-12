import Dubon2026.GaloisTowerQuotientUnitCoefficients
import Dubon2026.OriginalGroupChangeCohomologyIsomorphism
import Dubon2026.OriginalSecondCohomologyInflationRestriction

/-! # Genuine algebraic unit H2 inflation is injective in every finite Galois field tower -/

namespace Dubon2026
noncomputable section

open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable (K L M : Type) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [FiniteDimensional K M] [FiniteDimensional L M] [IsGalois K L] [IsGalois K M]

omit [FiniteDimensional K M] in
/-- The actual quotient-kernel coefficient comparison followed by
original H2 inflation is exactly the original finite field-tower map,
as an equality of maps induced by the same original cochains. -/
theorem finiteGaloisUnitH2Inflation_composition :
    groupCohomology.map (galoisTowerQuotientEquiv K L M).toMonoidHom
        (galoisTowerQuotientUnitInclusion K L M) 2 ≫
      (originalSecondCohomologyInfRes (Rep.ofAlgebraAutOnUnits K M)
        (AlgEquiv.restrictNormalHom L : Gal(M/K) →* Gal(L/K)).ker
        (galoisTowerKernelUnit_first_zero K L M)).f =
    groupCohomology.map (AlgEquiv.restrictNormalHom L)
      (finiteGaloisUnitTowerInclusion K L M) 2 := by
  change HomologicalComplex.homologyMap _ 2 ≫ HomologicalComplex.homologyMap _ 2 = _
  rw [← HomologicalComplex.homologyMap_comp]
  apply congrArg (fun t : groupCohomology.inhomogeneousCochains
      (Rep.ofAlgebraAutOnUnits K L) ⟶
      groupCohomology.inhomogeneousCochains (Rep.ofAlgebraAutOnUnits K M) =>
    HomologicalComplex.homologyMap t 2)
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext g
  rfl

/-- Actual finite Galois field-tower H2 inflation is injective. Its
coefficient inclusion, group restriction and kernel H1 are the original
ones, with kernel H1 vanishing derived from genuine Hilbert90. -/
theorem finiteGaloisUnitH2Inflation_mono :
    Mono (groupCohomology.map (AlgEquiv.restrictNormalHom L)
      (finiteGaloisUnitTowerInclusion K L M) 2) := by
  let S := (AlgEquiv.restrictNormalHom L : Gal(M/K) →* Gal(L/K)).ker
  haveI : Mono (galoisTowerQuotientUnitInclusion K L M) :=
    (Rep.mono_iff_injective _).mpr (galoisTowerQuotientUnitInclusion_bijective K L M).1
  haveI : Epi (galoisTowerQuotientUnitInclusion K L M) :=
    (Rep.epi_iff_surjective _).mpr (galoisTowerQuotientUnitInclusion_bijective K L M).2
  haveI : IsIso (galoisTowerQuotientUnitInclusion K L M) := isIso_of_mono_of_epi _
  haveI : IsIso (groupCohomology.map (galoisTowerQuotientEquiv K L M).toMonoidHom
      (galoisTowerQuotientUnitInclusion K L M) 2) :=
    originalGroupChangeCohomology_isIso (Rep.ofAlgebraAutOnUnits K L)
      ((Rep.ofAlgebraAutOnUnits K M).quotientToInvariants S)
      (galoisTowerQuotientEquiv K L M) (galoisTowerQuotientUnitInclusion K L M) 2
  haveI : Mono (originalSecondCohomologyInfRes (Rep.ofAlgebraAutOnUnits K M) S
      (galoisTowerKernelUnit_first_zero K L M)).f :=
    originalSecondCohomology_inflation_mono (Rep.ofAlgebraAutOnUnits K M) S
      (galoisTowerKernelUnit_first_zero K L M)
  rw [← finiteGaloisUnitH2Inflation_composition K L M]
  apply (ModuleCat.mono_iff_injective _).mpr
  exact ((ModuleCat.mono_iff_injective
    (originalSecondCohomologyInfRes (Rep.ofAlgebraAutOnUnits K M) S
      (galoisTowerKernelUnit_first_zero K L M)).f).mp inferInstance).comp
    (asIso (groupCohomology.map (galoisTowerQuotientEquiv K L M).toMonoidHom
      (galoisTowerQuotientUnitInclusion K L M) 2)).toLinearEquiv.injective

end
end Dubon2026
