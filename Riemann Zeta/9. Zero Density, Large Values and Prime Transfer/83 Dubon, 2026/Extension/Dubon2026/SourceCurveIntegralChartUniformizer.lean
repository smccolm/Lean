import Dubon2026.SourceIntegralChartPoleBound
import Dubon2026.SourceCurveChartOrders
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-! DUB-17/18 -> good reduction -> principal-divisor pushforward -> local
fiber-order inequality. A uniformizer can be chosen integral over the
separating coordinate chart. Native Dedekind uniformizers and the existing
normalized center-order identity replace the external approximation and
pole-cancellation construction. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open scoped IntermediateField.algebraAdjoinAdjoin

theorem exists_chart_uniformizer
    {K F R : Type*} [Field K] [Field F] [Algebra K F]
    [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
    (Q : Place K F) (hR : ∀ r : R, algebraMap R F r ∈ Q.toValuationSubring) :
    ∃ t : R, Q.ord (algebraMap R F t) = 1 := by
  let P := centerHeightOneSpectrum R Q hR
  obtain ⟨t, ht⟩ := P.valuation_exists_uniformizer' F
  change P.valuation F (algebraMap R F t) = WithZero.exp (-1) at ht
  have ht0 : algebraMap R F t ≠ 0 := by
    intro he
    rw [he, map_zero] at ht
    exact WithZero.exp_ne_zero ht.symm
  refine ⟨t, ?_⟩
  rw [ord_eq_neg_log_center_valuation Q hR ht0, ht, WithZero.log_exp]
  norm_num

theorem exists_integral_chart_uniformizer
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F]
    (Q : Place K F) (hxQ : x ∈ Q.toValuationSubring) :
    ∃ t : F, IsIntegral (Algebra.adjoin K {x}) t ∧ Q.ord t = 1 := by
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
  have hC : ∀ c : C, algebraMap C F c ∈ Q.toValuationSubring :=
    fun c => Q.mem_of_integral_adjoin hxQ c.2
  obtain ⟨t, ht⟩ := exists_chart_uniformizer Q hC
  exact ⟨(t : F), t.2, ht⟩

end
end Dubon2026.SourceCurve.Place
