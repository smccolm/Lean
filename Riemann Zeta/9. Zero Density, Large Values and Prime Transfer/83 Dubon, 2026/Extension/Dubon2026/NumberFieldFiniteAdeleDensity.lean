import Dubon2026.NumberFieldIntegralProductDensity
import Dubon2026.NumberFieldFiniteAdeleDenominator
import Dubon2026.NumberFieldIntegralFiniteAdelesCompact

/-! # Strong approximation in the original number-field finite adeles

The repository's rational denominator-and-closure proof applies directly
once simultaneous integral approximation is available for the original
ring of integers. This supplies DUB-17's local recovery of the attached
adelic lattices, with the actual restricted-product topology retained.
-/

namespace Dubon2026

noncomputable section

open NumberField IsDedekindDomain Topology
open scoped NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- Every original integral adele is in the closure of the original number-field diagonal. -/
theorem numberFieldIntegralProduct_mem_principal_closure
    (x : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K) :
    numberFieldIntegralFiniteAdeleMap K x ∈
      closure (Set.range (algebraMap K (FiniteAdeleRing (𝓞 K) K))) := by
  refine (numberFieldIntegers_dense_integral_product K).induction_on x
    (isClosed_closure.preimage (numberFieldIntegralFiniteAdeleMap_continuous K)) ?_
  intro r
  exact subset_closure ⟨(r : K), rfl⟩

/-- The original number field is dense in its original finite adele ring. -/
theorem numberField_dense_finiteAdeles :
    DenseRange (algebraMap K (FiniteAdeleRing (𝓞 K) K)) := by
  intro x
  obtain ⟨d, hd, hi⟩ := numberFieldFiniteAdele_exists_integral_multiple K x
  let y : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K :=
    fun v => ⟨(x * algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) d) v, hi v⟩
  let C := (algebraMap K (FiniteAdeleRing (𝓞 K) K)).range.topologicalClosure
  have hy : numberFieldIntegralFiniteAdeleMap K y ∈ C :=
    numberFieldIntegralProduct_mem_principal_closure K y
  have hinv : algebraMap K (FiniteAdeleRing (𝓞 K) K) (d : K)⁻¹ ∈ C :=
    Subring.le_topologicalClosure _ ⟨(d : K)⁻¹, rfl⟩
  have hmul := C.mul_mem hy hinv
  have hdK : (d : K) ≠ 0 := by
    intro hz
    exact hd (Subtype.ext hz)
  have he : numberFieldIntegralFiniteAdeleMap K y *
      algebraMap K (FiniteAdeleRing (𝓞 K) K) (d : K)⁻¹ = x := by
    change (x * algebraMap K (FiniteAdeleRing (𝓞 K) K) (d : K)) *
      algebraMap K (FiniteAdeleRing (𝓞 K) K) (d : K)⁻¹ = x
    rw [mul_assoc, ← map_mul, mul_inv_cancel₀ hdK, map_one, mul_one]
  rwa [he] at hmul

/-- Original number-field vectors are dense in the product of original finite adele rings. -/
theorem numberFieldVectors_dense_finiteAdeles (ι : Type*) :
    DenseRange (fun x : ι → K => fun i => algebraMap K (FiniteAdeleRing (𝓞 K) K) (x i)) :=
  DenseRange.piMap (fun _ => numberField_dense_finiteAdeles K)

end
end Dubon2026
