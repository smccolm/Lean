import Dubon2026.SourceCurvePrimePlaces
import Mathlib.RingTheory.EssentialFiniteness

/-! DUB-17/18 -> regular differential dimension -> canonical divisors ->
local integral differentials. The already identified actual place ring is a
localization of its Dedekind chart, so pinned essential-finiteness results
apply directly. This avoids the external general local-model framework.
-/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
variable (v : Place K F) (hR : ∀ r : R, algebraMap R F r ∈ v.toValuationSubring)

/-- The actual inclusion of an integral chart in the place ring. -/
@[reducible]
def chartAlgebra : Algebra R v.toValuationSubring :=
  ((algebraMap R F).codRestrict v.toValuationSubring.toSubring hR).toAlgebra

theorem isLocalization_at_center :
    letI := v.chartAlgebra hR
    IsLocalization (centerHeightOneSpectrum R v hR).asIdeal.primeCompl v.toValuationSubring := by
  letI := v.chartAlgebra hR
  let e : valuationSubringAtPrime F (centerHeightOneSpectrum R v hR) ≃ₐ[R]
      v.toValuationSubring :=
    AlgEquiv.ofRingEquiv (f := RingEquiv.subringCongr
      (congrArg ValuationSubring.toSubring (toValuationSubring_eq_of_forall_mem v hR).symm))
      (fun _ => rfl)
  exact IsLocalization.isLocalization_of_algEquiv _ e

variable [Algebra K R] [IsScalarTower K R F]

include hR in
theorem essFiniteType_of_chart [Algebra.EssFiniteType K R] :
    Algebra.EssFiniteType K v.toValuationSubring := by
  letI := v.chartAlgebra hR
  letI : IsScalarTower K R v.toValuationSubring := IsScalarTower.of_algebraMap_eq fun a => by
    apply Subtype.ext
    exact IsScalarTower.algebraMap_apply K R F a
  haveI := v.isLocalization_at_center hR
  haveI : Algebra.EssFiniteType R v.toValuationSubring :=
    Algebra.EssFiniteType.of_isLocalization _ (centerHeightOneSpectrum R v hR).asIdeal.primeCompl
  exact Algebra.EssFiniteType.comp K R v.toValuationSubring

end
end Dubon2026.SourceCurve.Place
