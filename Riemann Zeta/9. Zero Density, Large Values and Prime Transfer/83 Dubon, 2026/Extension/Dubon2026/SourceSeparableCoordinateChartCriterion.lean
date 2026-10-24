import Dubon2026.SourceCurveChartIntegralCriterion

/-! DUB-17/18 -> Kummer genus inequality -> finite residue-chart generation.
The actual modular j coordinate is separating in the residue characteristic.
The existing Dedekind-chart criterion therefore applies with separability
in place of characteristic zero. This supplies precisely the integral-chart
membership needed for finite-module generation, without a new Riemann--Roch
recurrence or a generic inseparable-coordinate development. -/
namespace Dubon2026.SourceCurve
noncomputable section
open scoped IntermediateField.algebraAdjoinAdjoin

theorem isIntegral_adjoin_of_nonnegative_orders_separating
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (t : F) (ht : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K {t}) F]
    [Algebra.IsSeparable (IntermediateField.adjoin K {t}) F] (x : F)
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
