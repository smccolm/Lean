import Dubon2026.SourceTrivialIntegralChange
import Dubon2026.SourceTrivialH1CharZeroSpan

/-! DUB-17/18 -> residual Galois association -> the actual characteristic-zero
weight-two Hecke action. The proved homomorphism-span result is identified
with the image of the actual native integral coefficient map. Consequently
integral Hecke relations hold on the entire original complex H1.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup groupCohomology

/-- The image of actual integral coefficient change spans the full original
complex trivial-coefficient H1. -/
theorem sourceTrivialComplexH1_span_integer (Q : ℕ) [NeZero Q] :
    Submodule.span ℂ (Set.range (sourceTrivialH1IntegerChange ℂ Q)) = ⊤ := by
  apply top_unique
  intro x hxTop
  clear hxTop
  have hx := sourceTrivialH1_mem_integralSpan_charZero Q ℂ x
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z, rfl⟩ := hy
    apply Submodule.subset_span
    refine ⟨(H1IsoOfIsTrivial (Rep.trivial ℤ (Gamma0 Q) ℤ)).inv z, ?_⟩
    change (H1IsoOfIsTrivial (Rep.trivial ℂ (Gamma0 Q) ℂ)).inv
      ((Int.castAddHom ℂ).comp
        ((H1IsoOfIsTrivial (Rep.trivial ℤ (Gamma0 Q) ℤ)).hom
          ((H1IsoOfIsTrivial (Rep.trivial ℤ (Gamma0 Q) ℤ)).inv z))) = _
    simp
  | zero => exact Submodule.zero_mem _
  | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
  | smul a y _ hy => exact Submodule.smul_mem _ a hy

/-- A complex operator vanishing on every actual integral H1 class vanishes
on the whole original complex H1, without a supplied spanning premise. -/
theorem sourceTrivialComplexH1_end_zero_of_integer (Q : ℕ) [NeZero Q]
    (T : Module.End ℂ (H1 (Rep.trivial ℂ (Gamma0 Q) ℂ)))
    (hT : ∀ x : H1 (Rep.trivial ℤ (Gamma0 Q) ℤ), T (sourceTrivialH1IntegerChange ℂ Q x) = 0) :
    T = 0 := by
  apply LinearMap.ext
  intro x
  have hx : x ∈ Submodule.span ℂ (Set.range (sourceTrivialH1IntegerChange ℂ Q)) := by
    rw [sourceTrivialComplexH1_span_integer]; trivial
  change T x = 0
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨z, rfl⟩ := hy; exact hT z
  | zero => exact map_zero T
  | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
  | smul a y _ hy => rw [map_smul, hy, smul_zero]

end
end Dubon2026
