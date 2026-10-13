import Dubon2026.OriginalIdeleClassH2Inflation
import Dubon2026.OriginalIdeleClassH2Restriction

/-! # Exact original idele-class H2 descent in finite Galois towers

An actual upper-stage class descends precisely when its actual relative
restriction vanishes. The coefficient comparisons, kernel H1 vanishing
and inflation-restriction exactness are all proved on the original groups.
This removes a finite-stage descent premise from the normalized global
class invariant needed for DUB-17's local sum formula and duality.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
variable (K E L : Type) [Field K] [Field E] [NumberField E] [Field L] [NumberField L]
  [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]
  [FiniteDimensional K L] [IsGalois K E] [IsGalois K L]

/-- An original class H2 element descends along the actual field tower exactly when its relative restriction vanishes. -/
theorem originalIdeleClassH2_inflation_exists_iff_restriction_zero
    (x : groupCohomology (originalIdeleClassRep K L) 2) :
    (∃ y : groupCohomology (originalIdeleClassRep K E) 2,
      groupCohomology.map (AlgEquiv.restrictNormalHom E)
        (originalIdeleClassTowerInclusion K E L) 2 y = x) ↔
      originalIdeleClassTowerH2Restriction K E L x = 0 := by
  let A := originalIdeleClassRep K L
  let S := (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K)).ker
  let X := originalSecondCohomologyInfRes A S (originalIdeleClassTowerKernel_first_zero K E L)
  let qmap := groupCohomology.map (galoisTowerQuotientEquiv K E L).toMonoidHom
    (originalIdeleClassTowerQuotientInclusion K E L) 2
  let smap := groupCohomology.map (galoisTowerKernelEquiv K E L).toMonoidHom
    (originalIdeleClassTowerKernelCoefficientIso K E L).hom 2
  haveI : Mono (originalIdeleClassTowerQuotientInclusion K E L) :=
    (Rep.mono_iff_injective _).mpr (originalIdeleClassTowerQuotientInclusion_bijective K E L).1
  haveI : Epi (originalIdeleClassTowerQuotientInclusion K E L) :=
    (Rep.epi_iff_surjective _).mpr (originalIdeleClassTowerQuotientInclusion_bijective K E L).2
  haveI : IsIso (originalIdeleClassTowerQuotientInclusion K E L) := isIso_of_mono_of_epi _
  haveI : IsIso qmap := originalGroupChangeCohomology_isIso
    (originalIdeleClassRep K E) (A.quotientToInvariants S)
    (galoisTowerQuotientEquiv K E L) (originalIdeleClassTowerQuotientInclusion K E L) 2
  haveI : IsIso smap := originalGroupChangeCohomology_isIso
    (originalIdeleClassRep E L) (Rep.res S.subtype A)
    (galoisTowerKernelEquiv K E L) (originalIdeleClassTowerKernelCoefficientIso K E L).hom 2
  have hinf (y : groupCohomology (originalIdeleClassRep K E) 2) :
      X.f (qmap y) = groupCohomology.map (AlgEquiv.restrictNormalHom E)
        (originalIdeleClassTowerInclusion K E L) 2 y := by
    exact congrArg (fun f : groupCohomology (originalIdeleClassRep K E) 2 ⟶
      groupCohomology A 2 => f y) (originalIdeleClassH2Inflation_composition K E L)
  have hres (y : groupCohomology A 2) :
      smap (originalIdeleClassTowerH2Restriction K E L y) = X.g y := by
    exact congrArg (fun f : groupCohomology A 2 ⟶ groupCohomology (Rep.res S.subtype A) 2 =>
      f y) (originalIdeleClassTowerH2Restriction_kernel_composition K E L)
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
      (originalIdeleClassTowerKernel_first_zero K E L)).moduleCat_range_eq_ker
    have hmem : x ∈ X.f.hom.range := by rw [hex]; exact hx'
    obtain ⟨q, hq⟩ := hmem
    obtain ⟨y, hy⟩ := (asIso qmap).toLinearEquiv.surjective q
    exact ⟨y, (hinf y).symm.trans ((congrArg X.f hy).trans hq)⟩

end
end Dubon2026
