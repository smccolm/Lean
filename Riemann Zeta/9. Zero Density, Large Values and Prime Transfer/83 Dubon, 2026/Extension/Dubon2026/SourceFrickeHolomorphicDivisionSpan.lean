import Dubon2026.SourceFrickeHolomorphicDivisionInvariance

/-! DUB-17/18 -> actual Gamma1 cusp realization -> rational cusp-form spanning
-> elliptic divisibility transport. A holomorphic quotient of actual Fricke
span functions is again in the span. Original Laurent germs prove that all
its translated cusps are meromorphic; the proved discriminant pole-clearing
and actual function-spanning theorems discharge the remaining hypotheses.
No cusp-growth or quotient-span assumption is introduced. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField
open scoped MatrixGroups Manifold

theorem exists_frickeSpan_laurent {N : ℕ} [NeZero N] {F : ℍ → ℂ}
    (hF : F ∈ Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N)) :
    ∃ A : LaurentSeries ℂ, CuspTaylor.Represents A (cuspFunction N F) := by
  obtain ⟨A, hA, _⟩ := exists_fricke_twist_laurent N AlgEquiv.refl ⟨F, hF⟩
  exact ⟨A, hA⟩

theorem meromorphic_cusp_holomorphic_quotient {N : ℕ} [NeZero N]
    {F G W : ℍ → ℂ} (hF : F ∈ Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N))
    (hG : G ∈ Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N))
    (hG0 : G ≠ 0) (hrel : W * G = F) : MeromorphicAt (cuspFunction N W) 0 := by
  obtain ⟨A, hA⟩ := exists_frickeSpan_laurent hF
  obtain ⟨B, hB⟩ := exists_frickeSpan_laurent hG
  have hB0 := hB.ne_zero_of_function_ne_zero (by exact_mod_cast NeZero.pos N)
    (frickeSpan_holomorphic hG) (frickeSpan_periodic hG) hG0
  exact (hA.cusp_of_mul_eq hB hB0 hrel).meromorphicAt

theorem mem_frickeSpan_of_holomorphic_quotient {N : ℕ} [NeZero N]
    {F G W : ℍ → ℂ} (hF : F ∈ Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N))
    (hG : G ∈ Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N))
    (hG0 : G ≠ 0) (hW : MDiff W) (hrel : W * G = F) :
    W ∈ Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N) := by
  apply mem_span_holomorphic_cyclotomic_fractions_of_principal_invariant W hW
    (principalInvariant_holomorphic_quotient hF hG hG0 hW hrel)
  intro γ
  have hFγ := smul_mem_frickeSpan γ⁻¹ hF
  have hGγ := smul_mem_frickeSpan γ⁻¹ hG
  have hGγ0 : γ⁻¹ • G ≠ (0 : ℍ → ℂ) := by
    intro hz
    apply hG0
    simpa only [smul_inv_smul, smul_zero] using congrArg (fun g : ℍ → ℂ => γ • g) hz
  have hWγ := mdifferentiable_slFn hW γ⁻¹
  have he : (γ⁻¹ • W) * (γ⁻¹ • G) = γ⁻¹ • F := by rw [← smul_mul', hrel]
  have hper := periodic_of_principal_invariant
    (principalInvariant_holomorphic_quotient hFγ hGγ hGγ0 hWγ he)
  obtain ⟨m, hm⟩ := exists_bounded_mul_discriminant_of_meromorphic hper
    (meromorphic_cusp_holomorphic_quotient hFγ hGγ hGγ0 he)
  refine ⟨m, ?_⟩
  simpa only [sl_smul_def, inv_inv, Function.comp_def] using hm

end
end Dubon2026.SourceFricke