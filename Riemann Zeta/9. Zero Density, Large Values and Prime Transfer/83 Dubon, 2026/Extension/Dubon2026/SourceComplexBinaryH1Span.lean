import Dubon2026.SourceComplexBinaryCocycleSpan

/-! The original complex H1 is spanned by integral classes.
DUB-17/18 -> residual modular Galois association -> the integral H1 Hecke
character. Integral operator relations can now be tested on the actual
complex period eigenclass because the genuine coefficient-change image spans.
No surjectivity of reduction in positive characteristic is asserted.
-/

namespace Dubon2026
noncomputable section

/-- Actual integral H1 classes span the full native complex binary H1 at the original level and weight. -/
theorem sourceComplexBinaryH1_span_integer (Q w : ℕ) [NeZero Q] :
    Submodule.span ℂ
      (Set.range (sourceBinaryH1Change (Int.castRingHom ℂ) Q w)) = ⊤ := by
  apply top_unique
  intro x _
  refine groupCohomology.H1_induction_on x ?_
  intro c
  have hc : c ∈ Submodule.span ℂ
      (Set.range (sourceBinaryCocyclesChange (Int.castRingHom ℂ) Q w)) := by
    rw [sourceComplexBinaryCocycles_span_integer]
    trivial
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨z, rfl⟩ := hc
    rw [← sourceBinaryH1Change_cocycle]
    exact Submodule.subset_span (Set.mem_range_self _)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add c d _ _ hc hd => rw [map_add]; exact Submodule.add_mem _ hc hd
  | smul a c _ hc => rw [map_smul]; exact Submodule.smul_mem _ _ hc

/-- A complex endomorphism that vanishes on the actual integral coefficient-change image
vanishes on the full source binary H1. -/
theorem sourceComplexBinaryH1_end_zero_of_integer (Q w : ℕ) [NeZero Q]
    (T : Module.End ℂ (groupCohomology.H1 (sourceBinaryCoefficientRep ℂ Q w)))
    (hT : ∀ x : groupCohomology.H1 (sourceBinaryCoefficientRep ℤ Q w),
      T (sourceBinaryH1Change (Int.castRingHom ℂ) Q w x) = 0) :
    T = 0 := by
  apply LinearMap.ext
  intro x
  have hx : x ∈ Submodule.span ℂ
      (Set.range (sourceBinaryH1Change (Int.castRingHom ℂ) Q w)) := by
    rw [sourceComplexBinaryH1_span_integer]
    trivial
  change T x = 0
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨z, rfl⟩ := hx; exact hT z
  | zero => exact map_zero T
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul a x _ hx => rw [map_smul, hx, smul_zero]

end
end Dubon2026
