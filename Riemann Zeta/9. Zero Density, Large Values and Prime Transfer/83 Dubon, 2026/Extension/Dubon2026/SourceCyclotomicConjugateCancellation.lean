import Dubon2026.SourceFrickeCyclotomicConjugateRelation

/-! DUB-17/18 -> actual Gamma1 differential realization -> rational Fourier
structure -> modular covariance of analytic cyclotomic conjugation. The
literal Laurent relation preserves nonzero original denominators and passes
through their actual function identities, including removable zeros. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField
open scoped MatrixGroups Manifold ModularForm

theorem cyclotomicLevelRing_holomorphicFraction {N : ℕ} [NeZero N] {F : ℍ → ℂ}
    (hF : F ∈ cyclotomicLevelRing N) : F ∈ holomorphicCyclotomicFrickeFractions N :=
  ⟨cyclotomicLevelRing_holomorphic hF, F, hF, 1, one_mem _, one_ne_zero, mul_one _⟩

theorem CyclotomicConjugates.of_mul_eq {N : ℕ} [NeZero N] {σ : kN N ≃ₐ[ℚ] kN N}
    {A B A' B' F G : ℍ → ℂ} (hAA' : CyclotomicConjugates σ A A')
    (hBB' : CyclotomicConjugates σ B B')
    (hB : B ∈ holomorphicCyclotomicFrickeFractions N) (hB0 : B ≠ 0)
    (hFA : F * B = A) (hGA' : G * B' = A') : CyclotomicConjugates σ F G := by
  obtain ⟨X, hX, hXA'⟩ := hAA'
  obtain ⟨Y, hY, hYB'⟩ := hBB'
  have hY0 := hY.ne_zero_of_function_ne_zero (by exact_mod_cast NeZero.pos N)
    hB.1 (holomorphicCyclotomicFrickeFractions_periodic hB) hB0
  have hY0' : Y ≠ 0 := fun hz => hY0 (by rw [hz, map_zero])
  have hYσ0 : coeffMap (algebraMap (kN N) ℂ) (coeffMap σ.toRingEquiv.toRingHom Y) ≠ 0 := by
    intro hz
    apply hY0'
    apply (coeffMap σ.toRingEquiv.toRingHom).injective
    apply (coeffMap (algebraMap (kN N) ℂ)).injective
    simpa only [map_zero] using hz
  refine ⟨X / Y, ?_, ?_⟩
  · rw [map_div₀]
    exact hX.cusp_of_mul_eq hY hY0 hFA
  · rw [map_div₀, map_div₀]
    exact hXA'.cusp_of_mul_eq hYB' hYσ0 hGA'

end
end Dubon2026.SourceFricke
