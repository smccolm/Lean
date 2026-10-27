import Dubon2026.SourceCuspWeightImageTwist
import Dubon2026.SourceAlgebraicallyClosedFixedField
import Dubon2026.SourceTwistStableSubspaceDescent

/-! DUB-17/18 -> actual Gamma1 cusp realization -> rational cusp-form spanning
-> fixed-field descent of the actual stable cusp image. The original
cyclotomic module is its literal inclusion into the proved complex Fricke
span. Its complex span is the whole ambient space, the actual coefficient
twists fix it pointwise, and the proved full complex fixed field supplies
the scalar descent premise. Stability remains explicit here and is derived
from the actual cusp-image consumer in the next step. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField

/-- The original cyclotomic Fricke module inside its actual complex span. -/
def originalFrickeSpan (N : ℕ) [NeZero N] :
    Submodule (kN N) (Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N)) :=
  LinearMap.range (cyclotomicFrickeSpanInclusion N)

theorem mem_originalFrickeSpan_iff {N : ℕ} [NeZero N]
    (F : Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N)) :
    F ∈ originalFrickeSpan N ↔ (F : ℍ → ℂ) ∈ holomorphicCyclotomicFrickeFractions N := by
  constructor
  · rintro ⟨G, rfl⟩
    exact G.property
  · intro hF
    exact ⟨⟨F, hF⟩, rfl⟩

theorem span_originalFrickeSpan_eq_top (N : ℕ) [NeZero N] :
    Submodule.span ℂ (originalFrickeSpan N : Set (Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N))) = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro F
  obtain ⟨n, c, G, rfl⟩ := exists_frickeSpan_sum_original F
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
    (Submodule.subset_span (show cyclotomicFrickeSpanInclusion N (G i) ∈ originalFrickeSpan N from ⟨G i, rfl⟩)))

theorem frickeCoefficientTwist_fixes_original_submodule (N : ℕ) [NeZero N]
    (σ : ℂ ≃ₐ[kN N] ℂ) {F : Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N)}
    (hF : F ∈ originalFrickeSpan N) : frickeCoefficientTwist N σ F = F := by
  obtain ⟨G, rfl⟩ := hF
  exact frickeCoefficientTwist_fixes_original N σ G

theorem frickeCoefficientTwist_sum_original_submodule (N : ℕ) [NeZero N]
    (σ : ℂ ≃ₐ[kN N] ℂ) {ι : Type} [Fintype ι] (c : ι → ℂ)
    (e : ι → Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N))
    (he : ∀ i, e i ∈ originalFrickeSpan N) :
    frickeCoefficientTwist N σ (∑ i, c i • e i) = ∑ i, σ (c i) • e i := by
  rw [map_sum]
  simp_rw [frickeCoefficientTwist_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [frickeCoefficientTwist_fixes_original_submodule N σ (he i)]

theorem mem_span_originalFrickeSpan_of_twist_stable (N : ℕ) [NeZero N]
    (V : Submodule ℂ (Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N)))
    (hV : ∀ σ : ℂ ≃ₐ[kN N] ℂ, ∀ F ∈ V, frickeCoefficientTwist N σ F ∈ V)
    {F : Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N)} (hF : F ∈ V) :
    F ∈ Submodule.span ℂ {G | G ∈ V ∧ G ∈ originalFrickeSpan N} := by
  apply TwistDescent.descent_generic (originalFrickeSpan N) V
    (by rw [span_originalFrickeSpan_eq_top]; exact le_top)
    (fun σ => frickeCoefficientTwist N σ)
    (fun σ ι _ c e he => frickeCoefficientTwist_sum_original_submodule N σ c e he) hV
    (fun c hc => ConstantFixedField.mem_range_of_fixed hc) hF

end
end Dubon2026.SourceFricke