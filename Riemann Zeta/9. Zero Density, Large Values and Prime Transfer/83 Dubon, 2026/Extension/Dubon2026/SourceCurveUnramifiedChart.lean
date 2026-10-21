import Dubon2026.SourceCurveRegularCoordinate
import Dubon2026.SourceCurveLocalChart
import Mathlib.RingTheory.Unramified.Basic

/-! DUB-17/18 -> canonical-divisor finite support. At an actual chart
center where the polynomial coordinate extension is unramified, pinned
localization transport gives integral generation by that coordinate's
derivative. Its normalized differential order is therefore zero. The next
consumer uses the finite different ideal to control the exceptional centers.
-/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open Polynomial IsDedekindDomain KaehlerDifferential

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable [Algebra K R] [Algebra K[X] R] [IsScalarTower K K[X] R]
variable [Algebra R F] [IsFractionRing R F] [IsScalarTower K R F]

theorem ordDifferential_coordinate_eq_zero_of_unramified
    (v : Place K F) (hR : ∀ r : R, algebraMap R F r ∈ v.toValuationSubring)
    [Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄K]]
    [Algebra.IsSeparable K v.ResidueField] [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    (hunr : Algebra.IsUnramifiedAt K[X] (center R v hR)) :
    v.ordDifferential (D K F (algebraMap R F (algebraMap K[X] R X))) = 0 := by
  letI := v.chartAlgebra hR
  letI : Algebra K[X] v.toValuationSubring :=
    ((algebraMap R v.toValuationSubring).comp (algebraMap K[X] R)).toAlgebra
  letI : IsScalarTower K[X] R v.toValuationSubring := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower K K[X] v.toValuationSubring := IsScalarTower.of_algebraMap_eq fun a => by
    apply Subtype.ext
    change algebraMap K F a = algebraMap R F (algebraMap K[X] R (algebraMap K K[X] a))
    rw [← IsScalarTower.algebraMap_apply K K[X] R, ← IsScalarTower.algebraMap_apply K R F]
  haveI : IsLocalization (center R v hR).primeCompl v.toValuationSubring :=
    v.isLocalization_at_center hR
  haveI : Algebra.FormallyUnramified K[X] (Localization.AtPrime (center R v hR)) := hunr
  let e : Localization.AtPrime (center R v hR) ≃ₐ[R] v.toValuationSubring :=
    IsLocalization.algEquiv (center R v hR).primeCompl _ _
  haveI : Algebra.FormallyUnramified K[X] v.toValuationSubring :=
    Algebra.FormallyUnramified.of_equiv (e.restrictScalars K[X])
  exact v.ordDifferential_D_eq_zero_of_integral_span
    (algebraMap K[X] v.toValuationSubring X) v.span_D_coordinate_of_formallyUnramified

end
end Dubon2026.SourceCurve.Place
