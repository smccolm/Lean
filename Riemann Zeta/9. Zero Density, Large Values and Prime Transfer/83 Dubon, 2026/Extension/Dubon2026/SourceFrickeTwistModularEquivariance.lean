import Dubon2026.SourceFrickeCyclotomicModularAction

/-! DUB-17/18 -> actual Gamma1 cusp realization -> rational cusp-form spanning
-> cusp conditions at every modular translate. The actual coefficient
twist commutes with the already proved pullback action because it fixes
every original cyclotomic fraction and twists every finite complex sum.
The cusp-vanishing equivalence therefore applies at every translated cusp. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField
open scoped MatrixGroups

theorem exists_frickeSpan_sum_original {N : ℕ} [NeZero N]
    (F : Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N)) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (G : Fin n → (cyclotomicHolomorphicFrickeAlgebra N).toSubmodule),
      F = ∑ i, c i • cyclotomicFrickeSpanInclusion N (G i) := by
  obtain ⟨n, c, g, hg⟩ := Submodule.mem_span_set'.mp F.property
  refine ⟨n, c, fun i => ⟨g i, (g i).property⟩, ?_⟩
  apply Subtype.ext
  simpa only [Submodule.coe_sum, Submodule.coe_smul] using hg.symm

theorem frickeCoefficientTwist_pullback (N : ℕ) [NeZero N] (σ : ℂ ≃ₐ[kN N] ℂ)
    (γ : SL(2, ℤ)) (F : Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N)) :
    frickeCoefficientTwist N σ (frickeSpanPullback N γ F) =
      frickeSpanPullback N γ (frickeCoefficientTwist N σ F) := by
  obtain ⟨n, c, G, rfl⟩ := exists_frickeSpan_sum_original F
  let H : Fin n → (cyclotomicHolomorphicFrickeAlgebra N).toSubmodule :=
    fun i => ⟨γ • (G i : ℍ → ℂ), smul_mem_holomorphicCyclotomicFrickeFractions γ (G i).property⟩
  have he : frickeSpanPullback N γ (∑ i, c i • cyclotomicFrickeSpanInclusion N (G i)) =
      ∑ i, c i • cyclotomicFrickeSpanInclusion N (H i) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
    rfl
  rw [he]
  apply Subtype.ext
  change (frickeCoefficientTwist N σ (∑ i, c i • cyclotomicFrickeSpanInclusion N (H i)) : ℍ → ℂ) =
    γ • (frickeCoefficientTwist N σ (∑ i, c i • cyclotomicFrickeSpanInclusion N (G i)) : ℍ → ℂ)
  rw [frickeCoefficientTwist_sum_original, frickeCoefficientTwist_sum_original, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (smul_comm γ (σ (c i)) (G i : ℍ → ℂ)).symm

theorem frickeCoefficientTwist_isZeroAtImInfty_sl_mul_discriminant_iff
    (N : ℕ) [NeZero N] (σ : ℂ ≃ₐ[kN N] ℂ) (γ : SL(2, ℤ))
    (F : Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N)) (m : ℕ) :
    IsZeroAtImInfty ((γ • (frickeCoefficientTwist N σ F : ℍ → ℂ)) * ⇑CuspForm.discriminant ^ m) ↔
      IsZeroAtImInfty ((γ • (F : ℍ → ℂ)) * ⇑CuspForm.discriminant ^ m) := by
  have h := frickeCoefficientTwist_isZeroAtImInfty_mul_discriminant_iff N σ
    (frickeSpanPullback N γ F) m
  rw [frickeCoefficientTwist_pullback] at h
  exact h

end
end Dubon2026.SourceFricke