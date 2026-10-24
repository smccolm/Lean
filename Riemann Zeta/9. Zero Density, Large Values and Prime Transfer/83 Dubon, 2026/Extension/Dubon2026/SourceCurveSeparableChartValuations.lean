import Dubon2026.SourceCurveDedekindValuationPlaces
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-! DUB-17/18 -> modular good reduction -> reduction-place comparison.
The finite separating residue coordinate supplies its actual Dedekind integral
chart. A proper valuation containing that coordinate is therefore a place.
Finiteness and separability remain explicit inputs to be supplied by the
already proved modular coefficient-field theorems. -/
namespace Dubon2026.SourceCurve
noncomputable section
open scoped IntermediateField.algebraAdjoinAdjoin

theorem exists_place_of_separable_chart
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F]
    (V : ValuationSubring F) (hK : ∀ c : K, algebraMap K F c ∈ V)
    (hxV : x ∈ V) (hV : V ≠ ⊤) :
    ∃ Q : Place K F, Q.toValuationSubring = V := by
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
  have hB : B.toSubring ≤ V.toSubring := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem z hz => obtain rfl : z = x := hz; exact hxV
    | algebraMap c => exact hK c
    | add a b _ _ ha hb => exact add_mem ha hb
    | mul a b _ _ ha hb => exact mul_mem ha hb
  letI : Algebra B V := (Subring.inclusion hB).toAlgebra
  haveI : IsScalarTower B V F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  apply exists_place_of_dedekind_chart (R := C) V hK ?_ hV
  intro c
  have hi : IsIntegral V (c : F) := c.2.tower_top
  obtain ⟨v, hv⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
  change (c : F) ∈ V
  exact hv ▸ v.2

end
end Dubon2026.SourceCurve
