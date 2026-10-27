import Dubon2026.SourceFrickeSpanMultiplication

/-! DUB-17/18 -> actual Gamma1 cusp realization -> rational cusp-form spanning
-> elliptic divisibility transport. The actual pointwise powers stay in the
proved function span and the coefficient twist preserves them. The later
elliptic argument uses these powers with the original j-coordinate factors. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField

theorem pow_mem_frickeSpan {N : ℕ} [NeZero N] {F : ℍ → ℂ}
    (hF : F ∈ Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N)) (n : ℕ) :
    F ^ n ∈ Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N) := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact Submodule.subset_span (cyclotomicHolomorphicFrickeAlgebra N).one_mem
  | succ n ih => rw [pow_succ]; exact mul_mem_frickeSpan ih hF

/-- The actual pointwise power as an element of the complex Fricke span. -/
def frickeSpanPow (N : ℕ) [NeZero N]
    (F : Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N)) (n : ℕ) :
    Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N) :=
  ⟨(F : ℍ → ℂ) ^ n, pow_mem_frickeSpan F.property n⟩

theorem frickeCoefficientTwist_pow (N : ℕ) [NeZero N] (σ : ℂ ≃ₐ[kN N] ℂ)
    (F : Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N)) (n : ℕ) :
    (frickeCoefficientTwist N σ (frickeSpanPow N F n) : ℍ → ℂ) =
      (frickeCoefficientTwist N σ F : ℍ → ℂ) ^ n := by
  induction n with
  | zero =>
    have he : frickeSpanPow N F 0 = cyclotomicFrickeSpanInclusion N
        ⟨1, (cyclotomicHolomorphicFrickeAlgebra N).one_mem⟩ := by
      apply Subtype.ext
      exact pow_zero _
    rw [he, frickeCoefficientTwist_fixes_original, pow_zero]
    rfl
  | succ n ih =>
    have he : frickeSpanPow N F (n + 1) = frickeSpanMul N (frickeSpanPow N F n) F := by
      apply Subtype.ext
      exact pow_succ _ n
    rw [he, frickeCoefficientTwist_mul, ih, pow_succ]

end
end Dubon2026.SourceFricke