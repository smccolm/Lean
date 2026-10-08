import Dubon2026.AdelicRaisingLieModule

/-! # Exact equality of the original raising span and original enveloping-algebra cyclic span -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

private theorem enveloping_preserves {W : Type*} [AddCommGroup W] [Module ℂ W]
    (T : UniversalEnvelopingAlgebra ℂ ComplexSl2 →ₐ[ℂ] Module.End ℂ W) (p : Submodule ℂ W)
    (hgen : ∀ x w, w ∈ p → T (UniversalEnvelopingAlgebra.ι ℂ x) w ∈ p)
    (z : UniversalEnvelopingAlgebra ℂ ComplexSl2) (v : W) (hv : v ∈ p) : T z v ∈ p := by
  have h : ∀ z : UniversalEnvelopingAlgebra ℂ ComplexSl2, ∀ w ∈ p, T z w ∈ p := by
    intro z
    apply universalEnveloping_induction (fun z => ∀ w ∈ p, T z w ∈ p)
    · intro a w hw
      rw [T.commutes a]
      exact p.smul_mem a hw
    · exact hgen
    · intro a b ha hb w hw
      rw [map_add, LinearMap.add_apply]
      exact p.add_mem (ha w hw) (hb w hw)
    · intro a b ha hb w hw
      rw [map_mul, Module.End.mul_apply]
      exact ha _ (hb w hw)
  exact h z v hv

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The full genuine enveloping algebra preserves the actual original raising span. -/
theorem adelicRaisingSpan_enveloping (hf : f ≠ 0)
    (z : UniversalEnvelopingAlgebra ℂ ComplexSl2) (v : adelicRealSmoothSubmodule f)
    (hv : v ∈ adelicRaisingSpan f) : adelicEnvelopingAction f z v ∈ adelicRaisingSpan f := by
  apply enveloping_preserves (adelicEnvelopingAction f) (adelicRaisingSpan f) _ z v hv
  intro x w hw
  rw [adelicEnvelopingAction_generator]
  exact adelicRaisingSpan_lie f hf x w hw

/-- Every actual raising derivative is the literal action of the corresponding power of the original enveloping generator. -/
theorem adelicRaisingJet_eq_enveloping (n : ℕ) :
    adelicRaisingJet f n = adelicEnvelopingAction f
      ((UniversalEnvelopingAlgebra.ι ℂ compactSl2E) ^ n) (adelicSmoothGenerator f) := by
  simp only [map_pow, adelicEnvelopingAction_generator, adelicRaisingJet]

/-- The original raising span is exactly the cyclic span of the original full enveloping action on the original generator. -/
theorem adelicRaisingSpan_eq_enveloping (hf : f ≠ 0) :
    adelicRaisingSpan f = Submodule.span ℂ (Set.range (fun z : UniversalEnvelopingAlgebra ℂ ComplexSl2 =>
      adelicEnvelopingAction f z (adelicSmoothGenerator f))) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    rw [adelicRaisingJet_eq_enveloping]
    exact Submodule.subset_span ⟨_, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨z, rfl⟩
    exact adelicRaisingSpan_enveloping f hf z _ (adelicSmoothGenerator_mem_raisingSpan f)

end
end Dubon2026
