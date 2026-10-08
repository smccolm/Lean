import Dubon2026.CanonicalAdicIntegralDensity
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

/-! # Rational strong approximation for the actual finite adele ring -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter Set
open scoped BigOperators

/-- The product of canonical local integer rings embeds into the actual finite adele ring. -/
def finiteAdeleIntegralEmbedding
    (x : ∀ v : HeightOneSpectrum ℤ, v.adicCompletionIntegers ℚ) : FiniteAdeleRing ℤ ℚ :=
  RestrictedProduct.structureMap (fun v : HeightOneSpectrum ℤ => v.adicCompletion ℚ)
    (fun v => (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))) cofinite x

/-- The integral-product embedding has its genuine product and restricted-product topologies. -/
theorem finiteAdeleIntegralEmbedding_continuous : Continuous finiteAdeleIntegralEmbedding :=
  RestrictedProduct.isEmbedding_structureMap.continuous

/-- Integral diagonal elements agree in the product and in the canonical rational adele algebra. -/
theorem finiteAdeleIntegralEmbedding_int (n : ℤ) :
    finiteAdeleIntegralEmbedding (fun v => (n : v.adicCompletionIntegers ℚ)) =
      algebraMap ℚ (FiniteAdeleRing ℤ ℚ) (n : ℚ) := by
  apply FiniteAdeleRing.ext
  intro v
  change (n : v.adicCompletion ℚ) = algebraMap ℚ (v.adicCompletion ℚ) (n : ℚ)
  simp

/-- One nonzero global integer clears every denominator of a genuine finite adele. -/
theorem finiteAdele_exists_integral_multiple (x : FiniteAdeleRing ℤ ℚ) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ v : HeightOneSpectrum ℤ,
      x v * (d : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ := by
  classical
  have hf : {v : HeightOneSpectrum ℤ | x v ∉ v.adicCompletionIntegers ℚ}.Finite :=
    Filter.eventually_cofinite.mp x.property
  choose b hb hi using (fun v : HeightOneSpectrum ℤ =>
    adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v (x v))
  have hi' (v : HeightOneSpectrum ℤ) :
      x v * (b v : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ := by
    have h := hi v
    change x v * algebraMap ℤ (v.adicCompletion ℚ) (b v) ∈ _ at h
    rw [show algebraMap ℤ (v.adicCompletion ℚ) = Int.castRingHom _ from
      Subsingleton.elim _ _] at h
    exact h
  let S := hf.toFinset
  let d : ℤ := ∏ v ∈ S, b v
  refine ⟨d, Finset.prod_ne_zero_iff.mpr (fun v _ => nonZeroDivisors.ne_zero (hb v)), ?_⟩
  intro v
  by_cases hv : v ∈ S
  · obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem b hv
    change d = b v * c at hc
    rw [hc, Int.cast_mul, ← mul_assoc]
    exact (v.adicCompletionIntegers ℚ).toSubring.mul_mem (hi' v) (by simp)
  · have hx : x v ∈ v.adicCompletionIntegers ℚ := by
      simpa only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] using hv
    exact (v.adicCompletionIntegers ℚ).toSubring.mul_mem hx (by simp)

/-- Every integral adele lies in the closure of the actual rational diagonal. -/
theorem finiteAdeleIntegralEmbedding_mem_rational_closure
    (x : ∀ v : HeightOneSpectrum ℤ, v.adicCompletionIntegers ℚ) :
    finiteAdeleIntegralEmbedding x ∈
      closure (Set.range (algebraMap ℚ (FiniteAdeleRing ℤ ℚ))) := by
  refine integer_dense_adic_integer_product.induction_on x
    (isClosed_closure.preimage finiteAdeleIntegralEmbedding_continuous) ?_
  intro n
  rw [finiteAdeleIntegralEmbedding_int]
  exact subset_closure ⟨(n : ℚ), rfl⟩

/-- The rational diagonal is dense in Mathlib's canonical finite adele ring. -/
theorem rational_dense_finiteAdeles :
    DenseRange (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)) := by
  intro x
  obtain ⟨d, hd, hi⟩ := finiteAdele_exists_integral_multiple x
  let y : ∀ v : HeightOneSpectrum ℤ, v.adicCompletionIntegers ℚ :=
    fun v => ⟨x v * (d : v.adicCompletion ℚ), hi v⟩
  let C := (algebraMap ℚ (FiniteAdeleRing ℤ ℚ)).range.topologicalClosure
  have hy : finiteAdeleIntegralEmbedding y ∈ C :=
    finiteAdeleIntegralEmbedding_mem_rational_closure y
  have hdmem : algebraMap ℚ (FiniteAdeleRing ℤ ℚ) ((d : ℚ)⁻¹) ∈ C :=
    Subring.le_topologicalClosure _ ⟨(d : ℚ)⁻¹, rfl⟩
  have hmul := C.mul_mem hy hdmem
  have heq : finiteAdeleIntegralEmbedding y *
      algebraMap ℚ (FiniteAdeleRing ℤ ℚ) ((d : ℚ)⁻¹) = x := by
    apply FiniteAdeleRing.ext
    intro v
    change (x v * (d : v.adicCompletion ℚ)) *
      algebraMap ℚ (v.adicCompletion ℚ) ((d : ℚ)⁻¹) = x v
    have hdv : (d : v.adicCompletion ℚ) ≠ 0 := by
      intro hz
      have hz' : algebraMap ℚ (v.adicCompletion ℚ) (d : ℚ) =
          algebraMap ℚ (v.adicCompletion ℚ) 0 := by simpa only [map_intCast, map_zero] using hz
      have hdq := (algebraMap ℚ (v.adicCompletion ℚ)).injective hz'
      exact hd (Int.cast_eq_zero.mp hdq)
    simp only [map_inv₀, map_intCast, mul_assoc, mul_inv_cancel₀ hdv, mul_one]
  rwa [heq] at hmul

end
end Dubon2026
