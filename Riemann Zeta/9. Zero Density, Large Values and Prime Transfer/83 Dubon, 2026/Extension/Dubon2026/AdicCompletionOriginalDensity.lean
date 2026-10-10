import Dubon2026.AdicCompletionEvaluationKernels
import Mathlib.RingTheory.AdicCompletion.Topology

/-! # Density of the original ring in its genuine finitely generated adic completion -/

namespace Dubon2026
noncomputable section

variable {R : Type*} [CommRing R]

/-- Every actual completion element has an original-ring representative modulo each original ideal power. -/
theorem adicCompletion_original_approximation (I : Ideal R) (hI : I.FG)
    (x : AdicCompletion I R) (n : ℕ) :
    ∃ r : R, x - algebraMap R (AdicCompletion I R) r ∈
      (I.map (algebraMap R (AdicCompletion I R))) ^ n := by
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  refine ⟨r, ?_⟩
  rw [← Ideal.map_pow, ← adicCompletion_evaluation_kernel I hI n]
  change AdicCompletion.evalₐ I n (x - AdicCompletion.of I R r) = 0
  rw [map_sub, AdicCompletion.evalₐ_of, hr, sub_self]

/-- The original ring is dense in its actual completion for the topology of the extended original ideal. -/
theorem adicCompletion_original_dense (I : Ideal R) (hI : I.FG)
    [TopologicalSpace (AdicCompletion I R)]
    (h : IsAdic (I.map (algebraMap R (AdicCompletion I R)))) :
    DenseRange (algebraMap R (AdicCompletion I R)) := by
  intro x
  apply (mem_closure_iff_nhds_basis (h.hasBasis_nhds x)).mpr
  intro n _hn
  obtain ⟨r, hr⟩ := adicCompletion_original_approximation I hI x n
  refine ⟨algebraMap R (AdicCompletion I R) r, ⟨r, rfl⟩, ?_⟩
  refine ⟨algebraMap R (AdicCompletion I R) r - x, ?_, ?_⟩
  · simpa only [neg_sub] using
      ((I.map (algebraMap R (AdicCompletion I R))) ^ n).neg_mem hr
  · change x + (algebraMap R (AdicCompletion I R) r - x) =
      algebraMap R (AdicCompletion I R) r
    rw [← add_sub_assoc, add_comm x, add_sub_cancel_right]

end
end Dubon2026
