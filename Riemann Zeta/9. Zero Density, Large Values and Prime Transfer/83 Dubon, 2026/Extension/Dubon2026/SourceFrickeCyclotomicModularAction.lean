import Dubon2026.SourceFrickeTwistCuspVanishing

/-! DUB-17/18 -> actual Gamma1 cusp realization -> rational cusp-form spanning
-> coefficient descent compatible with every cusp. Reuse the existing
literal modular pullback action and generator transformation theorem to
prove stability of the original cyclotomic algebra and its actual
holomorphic fractions. No transformed-fraction hypothesis is assumed. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField
open scoped MatrixGroups Manifold

theorem smul_mem_cyclotomicLevelRing {N : ℕ} [NeZero N] (γ : SL(2, ℤ)) {f : ℍ → ℂ}
    (hf : f ∈ cyclotomicLevelRing N) : γ • f ∈ cyclotomicLevelRing N := by
  induction hf using Algebra.adjoin_induction with
  | mem f hf => exact Algebra.subset_adjoin (smul_mem_levelGen γ hf)
  | algebraMap c =>
    change algebraMap (kN N) (ℍ → ℂ) c ∈ cyclotomicLevelRing N
    exact Subalgebra.algebraMap_mem _ c
  | add f g _ _ hf hg => rw [smul_add]; exact Subalgebra.add_mem _ hf hg
  | mul f g _ _ hf hg => rw [smul_mul']; exact Subalgebra.mul_mem _ hf hg

theorem smul_mem_holomorphicCyclotomicFrickeFractions {N : ℕ} [NeZero N]
    (γ : SL(2, ℤ)) {f : ℍ → ℂ} (hf : f ∈ holomorphicCyclotomicFrickeFractions N) :
    γ • f ∈ holomorphicCyclotomicFrickeFractions N := by
  obtain ⟨hh, a, ha, b, hb, hb0, he⟩ := hf
  refine ⟨mdifferentiable_slFn hh γ, γ • a, smul_mem_cyclotomicLevelRing γ ha,
    γ • b, smul_mem_cyclotomicLevelRing γ hb, ?_, ?_⟩
  · intro hz
    apply hb0
    simpa only [inv_smul_smul, smul_zero] using congrArg (fun g : ℍ → ℂ => γ⁻¹ • g) hz
  · rw [← smul_mul', he]

theorem smul_mem_frickeSpan {N : ℕ} [NeZero N] (γ : SL(2, ℤ)) {f : ℍ → ℂ}
    (hf : f ∈ Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N)) :
    γ • f ∈ Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N) := by
  induction hf using Submodule.span_induction with
  | mem f hf => exact Submodule.subset_span (smul_mem_holomorphicCyclotomicFrickeFractions γ hf)
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add f g _ _ hf hg => rw [smul_add]; exact Submodule.add_mem _ hf hg
  | smul c f _ hf => rw [smul_comm]; exact Submodule.smul_mem _ c hf

/-- Restriction of the actual modular pullback to the proved complex Fricke span. -/
def frickeSpanPullback (N : ℕ) [NeZero N] (γ : SL(2, ℤ)) :
    Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N) →ₗ[ℂ]
      Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N) where
  toFun F := ⟨γ • (F : ℍ → ℂ), smul_mem_frickeSpan γ F.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end
end Dubon2026.SourceFricke