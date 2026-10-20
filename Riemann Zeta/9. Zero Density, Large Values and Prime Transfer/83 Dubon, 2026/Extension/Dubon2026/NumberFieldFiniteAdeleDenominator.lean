import Dubon2026.NumberFieldIntegralFiniteAdeles

/-! # Denominators for original adelic lattices

This extends the existing rational finite-adele denominator proof using
the pinned Dedekind completion denominator theorem. It is the first
arithmetic bridge from actual unitary adeles to finite integral lattices,
needed by DUB-17's finite arithmetic double-coset obligation. The common
trace form and its determinant bound remain separate obligations.
-/

namespace Dubon2026

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField BigOperators

variable (K : Type*) [Field K] [NumberField K]

/-- One nonzero algebraic integer clears every local denominator of an original finite adele. -/
theorem numberFieldFiniteAdele_exists_integral_multiple
    (x : FiniteAdeleRing (𝓞 K) K) :
    ∃ d : 𝓞 K, d ≠ 0 ∧
      x * algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) d ∈
        numberFieldIntegralFiniteAdeles K := by
  classical
  have hf : {v : HeightOneSpectrum (𝓞 K) | x v ∉ v.adicCompletionIntegers K}.Finite :=
    Filter.eventually_cofinite.mp x.property
  choose b hb hi using (fun v : HeightOneSpectrum (𝓞 K) =>
    adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v (x v))
  let S := hf.toFinset
  let d : 𝓞 K := ∏ v ∈ S, b v
  refine ⟨d, Finset.prod_ne_zero_iff.mpr (fun v _ => nonZeroDivisors.ne_zero (hb v)), ?_⟩
  intro v
  change x v * algebraMap (𝓞 K) (v.adicCompletion K) d ∈ v.adicCompletionIntegers K
  by_cases hv : v ∈ S
  · obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem b hv
    change d = b v * c at hc
    rw [hc, map_mul, ← mul_assoc]
    exact (v.adicCompletionIntegers K).toSubring.mul_mem (hi v)
      (v.coe_mem_adicCompletionIntegers c)
  · have hx : x v ∈ v.adicCompletionIntegers K := by
      simpa only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] using hv
    exact (v.adicCompletionIntegers K).toSubring.mul_mem hx
      (v.coe_mem_adicCompletionIntegers d)

/-- A finite family of original adeles has a common nonzero integral denominator. -/
theorem numberFieldFiniteAdeles_exists_common_integral_multiple
    {ι : Type*} [Fintype ι] (x : ι → FiniteAdeleRing (𝓞 K) K) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ ∀ i,
      x i * algebraMap (𝓞 K) (FiniteAdeleRing (𝓞 K) K) d ∈
        numberFieldIntegralFiniteAdeles K := by
  classical
  choose b hb hi using fun i => numberFieldFiniteAdele_exists_integral_multiple K (x i)
  refine ⟨∏ i, b i, Finset.prod_ne_zero_iff.mpr (fun i _ => hb i), ?_⟩
  intro i
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem b (Finset.mem_univ i)
  rw [hc, map_mul, ← mul_assoc]
  apply (numberFieldIntegralFiniteAdeles K).mul_mem (hi i)
  intro v
  exact v.coe_mem_adicCompletionIntegers c

end
end Dubon2026
