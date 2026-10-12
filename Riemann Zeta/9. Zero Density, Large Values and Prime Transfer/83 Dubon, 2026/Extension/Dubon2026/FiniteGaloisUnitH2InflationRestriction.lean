import Dubon2026.FiniteGaloisUnitH2InflationInjection
import Dubon2026.GaloisUnitTowerRestriction

/-! # Exact original unit H2 inflation and restriction in finite Galois towers -/

namespace Dubon2026
noncomputable section

open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable (K L M : Type) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [FiniteDimensional K M] [FiniteDimensional L M] [IsGalois K L] [IsGalois K M]

/-- The kernel of the actual field-tower restriction is exactly the
image of the literal field-tower inflation. Both maps use the original
field units and actual automorphisms; Hilbert90 discharges the kernel H1. -/
theorem finiteGaloisUnitH2_inflation_exists_iff_restriction_zero
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K M) 2) :
    (∃ y : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2,
      groupCohomology.map (AlgEquiv.restrictNormalHom L)
        (finiteGaloisUnitTowerInclusion K L M) 2 y = x) ↔
      galoisUnitTowerH2Restriction K L M x = 0 := by
  let A := Rep.ofAlgebraAutOnUnits K M
  let S := (AlgEquiv.restrictNormalHom L : Gal(M/K) →* Gal(L/K)).ker
  let X := originalSecondCohomologyInfRes A S (galoisTowerKernelUnit_first_zero K L M)
  let qmap := groupCohomology.map (galoisTowerQuotientEquiv K L M).toMonoidHom
    (galoisTowerQuotientUnitInclusion K L M) 2
  let smap := groupCohomology.map (galoisTowerKernelEquiv K L M).toMonoidHom
    (galoisTowerKernelUnitCoefficientIso K L M).hom 2
  haveI : Mono (galoisTowerQuotientUnitInclusion K L M) :=
    (Rep.mono_iff_injective _).mpr (galoisTowerQuotientUnitInclusion_bijective K L M).1
  haveI : Epi (galoisTowerQuotientUnitInclusion K L M) :=
    (Rep.epi_iff_surjective _).mpr (galoisTowerQuotientUnitInclusion_bijective K L M).2
  haveI : IsIso (galoisTowerQuotientUnitInclusion K L M) := isIso_of_mono_of_epi _
  haveI : IsIso qmap := originalGroupChangeCohomology_isIso
    (Rep.ofAlgebraAutOnUnits K L) (A.quotientToInvariants S)
    (galoisTowerQuotientEquiv K L M) (galoisTowerQuotientUnitInclusion K L M) 2
  haveI : IsIso smap := originalGroupChangeCohomology_isIso
    (Rep.ofAlgebraAutOnUnits L M) (Rep.res S.subtype A)
    (galoisTowerKernelEquiv K L M) (galoisTowerKernelUnitCoefficientIso K L M).hom 2
  have hinf (y : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) :
      X.f (qmap y) = groupCohomology.map (AlgEquiv.restrictNormalHom L)
        (finiteGaloisUnitTowerInclusion K L M) 2 y := by
    exact congrArg (fun f : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2 ⟶
      groupCohomology A 2 => f y) (finiteGaloisUnitH2Inflation_composition K L M)
  have hres (y : groupCohomology A 2) :
      smap (galoisUnitTowerH2Restriction K L M y) = X.g y := by
    exact congrArg (fun f : groupCohomology A 2 ⟶ groupCohomology (Rep.res S.subtype A) 2 =>
      f y) (galoisUnitTowerH2Restriction_kernel_composition K L M)
  constructor
  · rintro ⟨y, rfl⟩
    apply (asIso smap).toLinearEquiv.injective
    change smap _ = smap 0
    rw [map_zero, hres, ← hinf]
    exact congrArg (fun f : X.X₁ ⟶ X.X₃ => f (qmap y)) X.zero
  · intro hx
    have hx' : X.g x = 0 := by
      rw [← hres, hx, map_zero]
      rfl
    have hex := (originalSecondCohomology_inflation_restriction_exact A S
      (galoisTowerKernelUnit_first_zero K L M)).moduleCat_range_eq_ker
    have hmem : x ∈ X.f.hom.range := by rw [hex]; exact hx'
    obtain ⟨q, hq⟩ := hmem
    obtain ⟨y, hy⟩ := (asIso qmap).toLinearEquiv.surjective q
    exact ⟨y, (hinf y).symm.trans ((congrArg X.f hy).trans hq)⟩

end
end Dubon2026
