import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-! # Extracting actual weight components from an invariant submodule -/

namespace Dubon2026

open scoped BigOperators

/-- Invariance under a diagonal operator with distinct weights forces every finite weight component into the original submodule. -/
theorem distinctWeight_component_mem {K W ι : Type*} [Field K] [AddCommGroup W] [Module K W]
    (T : Module.End K W) (v : ι → W) (μ : ι → K) (hμ : Function.Injective μ)
    (he : ∀ i, T (v i) = μ i • v i) (p : Submodule K W)
    (hp : ∀ w ∈ p, T w ∈ p) (s : Finset ι) (c : ι → K)
    (hs : ∑ i ∈ s, c i • v i ∈ p) : ∀ i ∈ s, c i • v i ∈ p := by
  classical
  induction s using Finset.induction_on generalizing c with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha] at hs
      have hdiff : ∑ i ∈ s, ((μ i - μ a) * c i) • v i ∈ p := by
        have h := p.sub_mem (hp _ hs) (p.smul_mem (μ a) hs)
        have hid : T (c a • v a + ∑ i ∈ s, c i • v i) -
            μ a • (c a • v a + ∑ i ∈ s, c i • v i) =
            ∑ i ∈ s, ((μ i - μ a) * c i) • v i := by
          simp only [map_add, map_smul, map_sum, he, smul_add, Finset.smul_sum, smul_smul]
          rw [mul_comm (c a) (μ a), add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          rw [← sub_smul]
          congr 1
          ring
        rwa [hid] at h
      have hrest : ∀ i ∈ s, c i • v i ∈ p := by
        intro i hi
        have h := ih (fun j => (μ j - μ a) * c j) hdiff i hi
        rw [mul_smul] at h
        exact (p.smul_mem_iff (sub_ne_zero.mpr (hμ.ne (ne_of_mem_of_not_mem hi ha)))).mp h
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · have h := p.sub_mem hs (p.sum_mem hrest)
        simpa only [add_sub_cancel_right] using h
      · exact hrest i hi

/-- A nonzero vector in a diagonal-invariant submodule of a weight span yields an original nonzero weight vector in that same submodule. -/
theorem distinctWeight_exists_mem {K W ι : Type*} [Field K] [AddCommGroup W] [Module K W]
    (T : Module.End K W) (v : ι → W) (μ : ι → K) (hμ : Function.Injective μ)
    (he : ∀ i, T (v i) = μ i • v i) (p : Submodule K W)
    (hp : ∀ w ∈ p, T w ∈ p) (w : W) (hw : w ∈ p) (hn : w ≠ 0)
    (hspan : w ∈ Submodule.span K (Set.range v)) : ∃ i, v i ∈ p ∧ v i ≠ 0 := by
  classical
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hspan
  change ∑ i ∈ c.support, c i • v i = w at hc
  have hn' : ∑ i ∈ c.support, c i • v i ≠ 0 := hc.trans_ne hn
  obtain ⟨i, hi, hci⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn'
  have hm := distinctWeight_component_mem T v μ hμ he p hp c.support c (hc ▸ hw) i hi
  have hcn : c i ≠ 0 := by intro h; apply hci; simp [h]
  refine ⟨i, (p.smul_mem_iff hcn).mp hm, ?_⟩
  intro h
  apply hci
  simp [h]

/-- In a span of distinct original weight vectors, an eigenvector of a specified weight lies on that original weight line. -/
theorem distinctWeight_eigenvector_eq_smul {K W ι : Type*} [Field K] [AddCommGroup W] [Module K W]
    (T : Module.End K W) (v : ι → W) (μ : ι → K) (hμ : Function.Injective μ)
    (he : ∀ i, T (v i) = μ i • v i) (i : ι) (w : W)
    (hw : w ∈ Submodule.span K (Set.range v)) (hTw : T w = μ i • w) :
    ∃ a : K, w = a • v i := by
  classical
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hw
  change ∑ j ∈ c.support, c j • v j = w at hc
  have hmem : ∀ j ∈ c.support, c j • v j ∈ T.eigenspace (μ i) := by
    apply distinctWeight_component_mem T v μ hμ he (T.eigenspace (μ i))
    · intro u hu
      rw [Module.End.mem_eigenspace_iff.mp hu]
      exact (T.eigenspace (μ i)).smul_mem _ hu
    · rw [hc]
      exact Module.End.mem_eigenspace_iff.mpr hTw
  refine ⟨c i, hc.symm.trans ?_⟩
  apply Finset.sum_eq_single i
  · intro j hj hji
    have h := Module.End.mem_eigenspace_iff.mp (hmem j hj)
    have hzero : (μ j - μ i) • (c j • v j) = 0 := by
      rw [sub_smul]
      apply sub_eq_zero.mpr
      calc
        μ j • (c j • v j) = c j • (μ j • v j) := smul_comm _ _ _
        _ = T (c j • v j) := by rw [map_smul, he]
        _ = μ i • (c j • v j) := h
    exact (smul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr (hμ.ne hji))
  · intro hi
    simp only [Finsupp.notMem_support_iff.mp hi, zero_smul]

end Dubon2026
