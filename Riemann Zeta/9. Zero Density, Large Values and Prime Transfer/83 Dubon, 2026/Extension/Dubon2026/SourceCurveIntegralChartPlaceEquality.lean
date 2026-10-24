import Dubon2026.SourceIntegralChartPoleBound
import Dubon2026.SourceCurvePlaceCenters
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-! DUB-17/18 -> modular good reduction -> uniqueness of the reduction place.
The existing Dedekind-chart center theorem identifies places from the
nonunits of integral chart functions. This replaces the external separating
function construction and its approximation argument. The modular residue
coordinate supplies finite separability in the actual consumer. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open scoped IntermediateField.algebraAdjoinAdjoin

theorem eq_of_integral_chart_nonunits
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F]
    (v w : Place K F) (hxv : x ∈ v.toValuationSubring) (hxw : x ∈ w.toValuationSubring)
    (he : ∀ g : F, IsIntegral (Algebra.adjoin K ({x} : Set F)) g →
      (g ∈ v.toValuationSubring.nonunits ↔ g ∈ w.toValuationSubring.nonunits)) : v = w := by
  let B := Algebra.adjoin K ({x} : Set F)
  haveI : IsPrincipalIdealRing B :=
    IsPrincipalIdealRing.of_surjective (Polynomial.algEquivOfTranscendental K x hx).toRingHom
      (Polynomial.algEquivOfTranscendental K x hx).surjective
  let C := integralClosure B F
  haveI : IsDedekindDomain C :=
    integralClosure.isDedekindDomain B (IntermediateField.adjoin K ({x} : Set F)) F
  haveI : IsFractionRing C F :=
    integralClosure.isFractionRing_of_finite_extension (A := B)
      (IntermediateField.adjoin K ({x} : Set F)) F
  have hv : ∀ c : C, algebraMap C F c ∈ v.toValuationSubring :=
    fun c => v.mem_of_integral_adjoin hxv c.2
  have hw : ∀ c : C, algebraMap C F c ∈ w.toValuationSubring :=
    fun c => w.mem_of_integral_adjoin hxw c.2
  have hc : center C v hv = center C w hw := by
    ext c
    rw [mem_center_iff, mem_center_iff,
      ← ValuationSubring.coe_mem_nonunits_iff, ← ValuationSubring.coe_mem_nonunits_iff]
    exact he (c : F) c.2
  have hp : centerHeightOneSpectrum C v hv = centerHeightOneSpectrum C w hw :=
    IsDedekindDomain.HeightOneSpectrum.ext hc
  apply Place.ext
  rw [toValuationSubring_eq_of_forall_mem v hv,
    toValuationSubring_eq_of_forall_mem w hw, hp]

end
end Dubon2026.SourceCurve.Place
