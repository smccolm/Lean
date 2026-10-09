import Dubon2026.AdelicIntegerRotationWeightSpace
import Dubon2026.AdelicSignedRaisingClosure

/-! # Every genuine integer-character projector on the original full real factor -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- On the entire original full real closure the genuine global signed-weight projector lands on its original signed raising line. -/
theorem adelicIntegerRotationWeightProjection_realClosure (hf : f ≠ 0) (hk : 0 < k)
    (i : ℕ ⊕ ℕ) (x : AdelicCyclicHilbert f) (hx : x ∈ (adelicFullRealUnitCore f).topologicalClosure) :
    adelicIntegerRotationWeightProjection f (adelicSignedRaisingWeight k i) x ∈
      Submodule.span ℂ {adelicSignedRaisingJet f i} := by
  rw [← adelicSignedRaisingClosedSpan_eq_fullRealClosure f hf] at hx
  let L : Submodule ℂ (AdelicCyclicHilbert f) := Submodule.span ℂ {adelicSignedRaisingJet f i}
  have hs : ∀ y ∈ Submodule.span ℂ (Set.range (adelicSignedRaisingJet f)),
      adelicIntegerRotationWeightProjection f (adelicSignedRaisingWeight k i) y ∈ L := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      by_cases hj : j = i
      · subst j
        rw [adelicIntegerRotationWeightProjection_signed f hf i]
        exact Submodule.subset_span (Set.mem_singleton _)
      · rw [adelicIntegerRotationWeightProjection_other f hf _ j
          ((adelicSignedRaisingWeight_injective k hk).ne (fun h => hj h.symm))]
        exact L.zero_mem
    | zero => simpa only [map_zero] using L.zero_mem
    | add y z hy hz ihy ihz => simpa only [map_add] using L.add_mem ihy ihz
    | smul c y hy ih => simpa only [map_smul] using L.smul_mem c ih
  exact closure_minimal hs (L.closed_of_finiteDimensional.preimage
    (adelicIntegerRotationWeightProjection f _).continuous) hx

/-- The true signed-weight projection of every full real orbit is a scalar multiple of its original signed raising vector. -/
theorem adelicIntegerRotationWeightProjection_realOrbit (hf : f ≠ 0) (hk : 0 < k)
    (i : ℕ ⊕ ℕ) (g : GeneralLinearGroup (Fin 2) ℝ) :
    ∃ c : ℂ, adelicIntegerRotationWeightProjection f (adelicSignedRaisingWeight k i)
      (adelicCyclicHilbertRepresentation f (adelicRealGL2Embedding g) (adelicCyclicHilbertGenerator f)) =
      c • adelicSignedRaisingJet f i := by
  have hx : adelicCyclicHilbertRepresentation f (adelicRealGL2Embedding g) (adelicCyclicHilbertGenerator f) ∈
      (adelicFullRealUnitCore f).topologicalClosure := by
    rw [adelicFullRealUnitCore_eq_generatorSpan f hf]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨g, rfl⟩)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
    (adelicIntegerRotationWeightProjection_realClosure f hf hk i _ hx)
  exact ⟨c, hc.symm⟩

end
end Dubon2026
