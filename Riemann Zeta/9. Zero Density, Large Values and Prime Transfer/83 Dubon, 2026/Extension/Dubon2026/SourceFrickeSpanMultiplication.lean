import Dubon2026.SourceFrickeTwistModularEquivariance
import Mathlib.Algebra.Algebra.Operations

/-! DUB-17/18 -> actual Gamma1 cusp realization -> rational cusp-form spanning
-> holomorphic divisibility at elliptic points. Products remain in the
actual Fricke function span by native multiplication of submodules. The
coefficient twist preserves actual products, as proved from finite sums
of original cyclotomic fractions, without assuming a multiplicative twist. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField
open scoped Pointwise

theorem mul_mem_frickeSpan {N : ℕ} [NeZero N] {F G : ℍ → ℂ}
    (hF : F ∈ Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N))
    (hG : G ∈ Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N)) :
    F * G ∈ Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N) := by
  have hle : Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N) *
      Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N) ≤
      Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N) := by
    rw [Submodule.span_mul_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨f, hf, g, hg, rfl⟩
    exact Submodule.subset_span (holomorphicCyclotomicFrickeFractions_mul hf hg)
  exact hle (Submodule.mul_mem_mul hF hG)

/-- Pointwise multiplication restricted to the actual complex Fricke span. -/
def frickeSpanMul (N : ℕ) [NeZero N]
    (F G : Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N)) :
    Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N) :=
  ⟨(F : ℍ → ℂ) * (G : ℍ → ℂ), mul_mem_frickeSpan F.property G.property⟩

theorem frickeCoefficientTwist_mul (N : ℕ) [NeZero N] (σ : ℂ ≃ₐ[kN N] ℂ)
    (F G : Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N)) :
    (frickeCoefficientTwist N σ (frickeSpanMul N F G) : ℍ → ℂ) =
      (frickeCoefficientTwist N σ F : ℍ → ℂ) * (frickeCoefficientTwist N σ G : ℍ → ℂ) := by
  obtain ⟨n, c, f, rfl⟩ := exists_frickeSpan_sum_original F
  obtain ⟨m, d, g, rfl⟩ := exists_frickeSpan_sum_original G
  let H : Fin n × Fin m → (cyclotomicHolomorphicFrickeAlgebra N).toSubmodule :=
    fun ij => ⟨(f ij.1 : ℍ → ℂ) * (g ij.2 : ℍ → ℂ),
      holomorphicCyclotomicFrickeFractions_mul (f ij.1).property (g ij.2).property⟩
  have hprod : ∀ (x : Fin n → ℂ) (y : Fin m → ℂ),
      (∑ i, x i • (f i : ℍ → ℂ)) * (∑ j, y j • (g j : ℍ → ℂ)) =
        ∑ ij : Fin n × Fin m, (x ij.1 * y ij.2) • (H ij : ℍ → ℂ) := by
    intro x y
    rw [Finset.sum_mul_sum, ← Finset.sum_product']
    apply Finset.sum_congr rfl
    intro ij _
    exact smul_mul_smul_comm _ _ _ _
  have he : frickeSpanMul N (∑ i, c i • cyclotomicFrickeSpanInclusion N (f i))
      (∑ j, d j • cyclotomicFrickeSpanInclusion N (g j)) =
      ∑ ij : Fin n × Fin m, (c ij.1 * d ij.2) • cyclotomicFrickeSpanInclusion N (H ij) := by
    apply Subtype.ext
    dsimp only [frickeSpanMul]
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using hprod c d
  rw [he, frickeCoefficientTwist_sum_original, frickeCoefficientTwist_sum_original,
    frickeCoefficientTwist_sum_original, hprod]
  simp only [map_mul]

end
end Dubon2026.SourceFricke