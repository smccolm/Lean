import Dubon2026.SourceCurvePrimePlaces
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! DUB-17/18 -> regular-differential cusp forms -> cusp decay -> integrality
over the inverse-j chart. The native intersection theorem for Dedekind
prime valuations, together with existing actual prime places, proves the
needed integral-closure criterion. This avoids a general valuation-ring
existence development and its separate polynomial-reversal argument.
-/
namespace Dubon2026.SourceCurve
noncomputable section
open IsDedekindDomain
open scoped IntermediateField.algebraAdjoinAdjoin

theorem mem_chart_of_mem_all_places
    {K F R : Type*} [Field K] [Field F] [Algebra K F]
    [CommRing R] [IsDedekindDomain R] [Algebra K R] [Algebra R F]
    [IsScalarTower K R F] [IsFractionRing R F] (x : F)
    (hx : ∀ v : Place K F, (∀ r : R, algebraMap R F r ∈ v.toValuationSubring) →
      x ∈ v.toValuationSubring) : x ∈ (algebraMap R F).range := by
  apply HeightOneSpectrum.mem_integers_of_valuation_le_one
  intro P
  exact hx (Place.ofHeightOneSpectrum P) (Place.algebraMap_mem_ofHeightOneSpectrum P)

theorem isIntegral_adjoin_of_nonnegative_orders
    {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K]
    (t : F) (ht : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K {t}) F] (x : F)
    (hx : ∀ v : Place K F, 0 ≤ v.ord t → 0 ≤ v.ord x) :
    IsIntegral (Algebra.adjoin K {t}) x := by
  let A := Algebra.adjoin K ({t} : Set F)
  let Kj := IntermediateField.adjoin K ({t} : Set F)
  letI : IsPrincipalIdealRing A :=
    IsPrincipalIdealRing.of_surjective (Polynomial.algEquivOfTranscendental K t ht).toRingEquiv.toRingHom
      (Polynomial.algEquivOfTranscendental K t ht).surjective
  letI : Algebra A Kj := (Subalgebra.inclusion
    (IntermediateField.algebra_adjoin_le_adjoin K ({t} : Set F))).toRingHom.toAlgebra
  letI : IsScalarTower A Kj F := Subalgebra.inclusion.isScalarTower_right
    (IntermediateField.algebra_adjoin_le_adjoin K ({t} : Set F)) _
  let B := integralClosure A F
  haveI : CharZero Kj := charZero_of_injective_algebraMap (algebraMap K Kj).injective
  haveI : IsDedekindDomain B := integralClosure.isDedekindDomain A Kj F
  haveI : IsFractionRing B F := integralClosure.isFractionRing_of_finite_extension Kj F
  have hmem : x ∈ (algebraMap B F).range := by
    apply mem_chart_of_mem_all_places (K := K)
    intro v hv
    apply v.mem_of_ord_nonneg
    apply hx
    apply v.ord_nonneg_of_mem
    have htA : t ∈ A := Algebra.subset_adjoin (Set.mem_singleton t)
    have hm := hv (algebraMap A B ⟨t, htA⟩)
    exact hm
  obtain ⟨y, hy⟩ := hmem
  exact hy ▸ y.2

end
end Dubon2026.SourceCurve
