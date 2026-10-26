import Dubon2026.SourceFrickeFunctionTransformationV2
import Dubon2026.SourceWeierstrassTorsionHolomorphy

/-! DUB-17/18 -> original all-weight arithmetic association -> finite Gamma1
character realization -> actual Picard/H1 and diamond comparison ->
differential realization -> rational Fourier structure -> Fricke generators.
The exact torsion series proves holomorphy of the original normalized
Weierstrass and Fricke functions for every nonzero torsion index. -/
namespace Dubon2026.SourceFricke
noncomputable section
open Complex PeriodPair
open UpperHalfPlane hiding I
open scoped Manifold MatrixGroups ModularForm

theorem frickeIdx_hyps {N : ℕ} [NeZero N] (a : Fin 2 → ZMod N) (ha : a ≠ 0) :
    (a 0).val < N ∧ (a 1).val < N ∧ ((a 0).val ≠ 0 ∨ (a 1).val ≠ 0) := by
  refine ⟨ZMod.val_lt _, ZMod.val_lt _, ?_⟩
  by_contra h
  push Not at h
  apply ha
  funext i
  fin_cases i
  · apply ZMod.val_injective N
    simpa using h.1
  · apply ZMod.val_injective N
    simpa using h.2

theorem mdifferentiable_wpNormZ {N : ℕ} [NeZero N]
    (a : Fin 2 → ZMod N) (ha : a ≠ 0) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (wpNormZ N a) := by
  obtain ⟨h₁, h₂, h₀⟩ := frickeIdx_hyps a ha
  have h := mdifferentiable_wpTorsion h₁ h₂ h₀
  change MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
    (fun τ => ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
      wpTorsion N (a 0).val (a 1).val τ)
  exact mdifferentiable_const.mul h

theorem mdifferentiable_frickeF {N : ℕ} [NeZero N]
    (a : Fin 2 → ZMod N) (ha : a ≠ 0) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (frickeF N a) := by
  have h₄ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (ModularForm.E₄ : ℍ → ℂ) :=
    ModularForm.E₄.holo'
  have h₆ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (ModularForm.E₆ : ℍ → ℂ) :=
    ModularForm.E₆.holo'
  have hΔ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (ModularForm.discriminant : ℍ → ℂ) :=
    CuspForm.discriminant.holo'
  exact (((h₄.mul h₆).div hΔ ModularForm.discriminant_ne_zero).neg.div
    mdifferentiable_const (by intro τ; norm_num)).mul (mdifferentiable_wpNormZ a ha)

end
end Dubon2026.SourceFricke
