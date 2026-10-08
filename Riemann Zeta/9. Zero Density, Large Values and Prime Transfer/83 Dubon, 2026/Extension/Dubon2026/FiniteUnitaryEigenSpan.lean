import Dubon2026.FiniteInvariantAnnihilator
import Dubon2026.PolynomialFiniteEigenSupport
import Dubon2026.HilbertFiniteCoordinateSpan
import Dubon2026.UnitaryEigenCoordinate

/-! # Actual finite invariant vectors have finite expansion in a simple unitary Hilbert eigenbasis -/

namespace Dubon2026

noncomputable section

/-- A vector in a genuine finite invariant subspace has finite actual Hilbert-basis expansion when an original unitary operator has distinct basis eigenvalues. -/
theorem finiteInvariant_mem_hilbert_eigen_span {V ι : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (W : Submodule ℂ V) (b : HilbertBasis ι ℂ W)
    (T : Module.End ℂ V) (hT : ∀ x y, inner ℂ (T x) (T y) = inner ℂ x y)
    (μ : ι → ℂ) (hμ : Function.Injective μ) (hμnorm : ∀ i, ‖μ i‖ = 1)
    (hb : ∀ i, T (b i).val = μ i • (b i).val)
    (U : Submodule ℂ V) [FiniteDimensional ℂ U] (hU : ∀ v ∈ U, T v ∈ U)
    (v : V) (hv : v ∈ W) (hu : v ∈ U) :
    v ∈ Submodule.span ℂ (Set.range (fun i => (b i).val)) := by
  let L : ι → V →ₗ[ℂ] ℂ := fun i => (innerSL ℂ (b i).val).toLinearMap
  obtain ⟨p, hp, hpv⟩ := finiteInvariant_polynomial_annihilator T U hU v hu
  have he (i : ι) (w : V) : L i (T w) = μ i * L i w :=
    unitary_eigen_coordinate T hT (b i).val (μ i) (hμnorm i) (hb i) w
  have hfin := polynomialAnnihilator_finite_eigen_support T L μ hμ he p hp v hpv
  have hcoords : Set.Finite {i | b.repr ⟨v, hv⟩ i ≠ 0} := by
    simpa only [HilbertBasis.repr_apply_apply] using hfin
  have hs := hilbertBasis_mem_span_of_finite_coordinates b ⟨v, hv⟩ hcoords
  have hm := Submodule.mem_map_of_mem (f := W.subtype) hs
  simpa only [Submodule.map_span, ← Set.range_comp, Function.comp_def, Submodule.subtype_apply] using hm

end
end Dubon2026
