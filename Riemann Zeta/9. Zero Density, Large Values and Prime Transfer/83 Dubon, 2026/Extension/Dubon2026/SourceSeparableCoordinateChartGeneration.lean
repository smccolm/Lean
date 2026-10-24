import Dubon2026.SourceSeparableCoordinateChartCriterion
import Dubon2026.SourceJointReductionPoleCharts
import Dubon2026.SourceCurvePoleBasisBound

/-! DUB-17/18 -> Kummer power lifting -> genus inequality -> finite generation
of the residue chart windows. The integral closure of a finite separating
coordinate is finite over the coordinate polynomial ring. Its actual finite
generators have a common pole bound, so their polynomial multiples generate
every function regular outside the coordinate poles. The modular coordinate's
already proved separability supplies this exact additional input. -/
namespace Dubon2026.SourceCurve
noncomputable section
open scoped IntermediateField.algebraAdjoinAdjoin

theorem exists_pole_space_generating_window_of_separating_coordinate
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (t : F) (ht : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F]
    (hsupport : {v : Place K F | v.ord t ≠ 0}.Finite) :
    ∃ M : ℕ, ∀ h : F, (∀ v : Place K F, 0 ≤ v.ord t → 0 ≤ v.ord h) →
      h ∈ Submodule.span K {g : F | ∃ j : ℕ,
        ∃ y ∈ LSpace (M • poleDivisor t hsupport), g = t ^ j * y} := by
  classical
  let A := Algebra.adjoin K ({t} : Set F)
  let Kt := IntermediateField.adjoin K ({t} : Set F)
  haveI : IsPrincipalIdealRing A :=
    IsPrincipalIdealRing.of_surjective (Polynomial.algEquivOfTranscendental K t ht).toRingHom
      (Polynomial.algEquivOfTranscendental K t ht).surjective
  let C := integralClosure A F
  haveI : Module.Finite A C := IsIntegralClosure.finite A Kt F C
  obtain ⟨n, b, hb⟩ := Module.Finite.exists_fin (R := A) (M := C)
  have hreg : ∀ i (v : Place K F), 0 ≤ v.ord t → 0 ≤ v.ord ((b i : C) : F) := by
    intro i v hv
    apply v.ord_nonneg_of_mem
    exact RegularProlongation.Joint.mem_valuation_of_integral_chart (b i).2
      v.toValuationSubring v.algebraMap_mem' (v.mem_of_ord_nonneg hv)
  obtain ⟨M, hM⟩ := exists_forall_mem_lSpace_nsmul_poleDivisor t hsupport
    (fun i => ((b i : C) : F)) hreg
  refine ⟨M, fun h hh => ?_⟩
  let SP : Submodule K F := Submodule.span K {g : F | ∃ j : ℕ,
    ∃ y ∈ LSpace (M • poleDivisor t hsupport), g = t ^ j * y}
  have hint : IsIntegral A h := isIntegral_adjoin_of_nonnegative_orders_separating t ht h hh
  let c : C := ⟨h, hint⟩
  have hc : c ∈ Submodule.span A (Set.range b) := by rw [hb]; trivial
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hc
  have hsum : h = ∑ i : Fin n, (a i : F) * ((b i : C) : F) := by
    have he := congrArg (integralClosure A F).val ha
    simp only [map_sum, Algebra.smul_def] at he
    exact he.symm
  rw [hsum]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨p, hp⟩ := Algebra.adjoin_eq_exists_aeval K t (a i)
  rw [← hp, Polynomial.aeval_eq_sum_range, Finset.sum_mul]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [smul_mul_assoc]
  exact SP.smul_mem _ (Submodule.subset_span ⟨j, (b i : F), hM i, rfl⟩)

end
end Dubon2026.SourceCurve
