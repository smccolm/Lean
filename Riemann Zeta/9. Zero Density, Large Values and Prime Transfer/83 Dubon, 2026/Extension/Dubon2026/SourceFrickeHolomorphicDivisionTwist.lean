import Dubon2026.SourceFrickeHolomorphicDivisionSpan

/-! DUB-17/18 -> actual Gamma1 cusp realization -> rational cusp-form spanning
-> elliptic divisibility transport. The proved holomorphic quotient span
closure allows a coefficient twist to transport an actual division identity
by an original cyclotomic function. Holomorphicity of the new quotient is
derived from the actual function span, not supplied as a descent hypothesis. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField
open scoped Manifold

theorem exists_twisted_holomorphic_quotient (N : ℕ) [NeZero N] (σ : ℂ ≃ₐ[kN N] ℂ)
    (F : Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N))
    (J : (cyclotomicHolomorphicFrickeAlgebra N).toSubmodule) (hJ0 : (J : ℍ → ℂ) ≠ 0)
    {W : ℍ → ℂ} (hW : MDiff W) (hrel : W * (J : ℍ → ℂ) = (F : ℍ → ℂ)) :
    ∃ W' : ℍ → ℂ, MDiff W' ∧ W' * (J : ℍ → ℂ) = (frickeCoefficientTwist N σ F : ℍ → ℂ) := by
  have hWs := mem_frickeSpan_of_holomorphic_quotient F.property
    (Submodule.subset_span J.property) hJ0 hW hrel
  let V : Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N) := ⟨W, hWs⟩
  have he : frickeSpanMul N V (cyclotomicFrickeSpanInclusion N J) = F := Subtype.ext hrel
  have ht := frickeCoefficientTwist_mul N σ V (cyclotomicFrickeSpanInclusion N J)
  rw [he, frickeCoefficientTwist_fixes_original] at ht
  exact ⟨frickeCoefficientTwist N σ V,
    frickeSpan_holomorphic (frickeCoefficientTwist N σ V).property, ht.symm⟩

end
end Dubon2026.SourceFricke