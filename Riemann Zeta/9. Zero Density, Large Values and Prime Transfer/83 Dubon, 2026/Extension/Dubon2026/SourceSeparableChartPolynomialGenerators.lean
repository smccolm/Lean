import Dubon2026.SourceSeparableCoordinateChartGeneration

/-! DUB-17/18 -> Kummer power lifting -> common residue constants -> finite
localized overlap. The actual separating residue coordinate makes its
integral closure finite. Native finite generators give polynomial
representations, with no finiteness assumption on the coefficient
valuation ring and no general inseparable normalization theorem. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
noncomputable section
open Polynomial
open scoped IntermediateField.algebraAdjoinAdjoin

theorem exists_integral_chart_polynomial_generators
    {k E : Type*} [Field k] [Field E] [Algebra k E]
    (x : E) (hx : Transcendental k x)
    [FiniteDimensional (IntermediateField.adjoin k ({x} : Set E)) E]
    [Algebra.IsSeparable (IntermediateField.adjoin k ({x} : Set E)) E] :
    ∃ (n : ℕ) (b : Fin n → E), ∀ h : E,
      IsIntegral (Algebra.adjoin k ({x} : Set E)) h →
        ∃ q : Fin n → k[X], h = ∑ i, aeval x (q i) * b i := by
  classical
  let D := Algebra.adjoin k ({x} : Set E)
  let Kx := IntermediateField.adjoin k ({x} : Set E)
  haveI : IsPrincipalIdealRing D :=
    IsPrincipalIdealRing.of_surjective (Polynomial.algEquivOfTranscendental k x hx).toRingHom
      (Polynomial.algEquivOfTranscendental k x hx).surjective
  let C := integralClosure D E
  haveI : Module.Finite D C := IsIntegralClosure.finite D Kx E C
  obtain ⟨n, b, hb⟩ := Module.Finite.exists_fin (R := D) (M := C)
  refine ⟨n, fun i => (b i : E), fun h hh => ?_⟩
  have hc : (⟨h, hh⟩ : C) ∈ Submodule.span D (Set.range b) := by rw [hb]; trivial
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun D).mp hc
  have he := congrArg (integralClosure D E).val ha
  simp only [map_sum, Algebra.smul_def] at he
  choose q hq using fun i => Algebra.adjoin_eq_exists_aeval k x (a i)
  refine ⟨q, he.symm.trans ?_⟩
  exact Finset.sum_congr rfl fun i _ => by rw [hq i]; rfl

end
end Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
