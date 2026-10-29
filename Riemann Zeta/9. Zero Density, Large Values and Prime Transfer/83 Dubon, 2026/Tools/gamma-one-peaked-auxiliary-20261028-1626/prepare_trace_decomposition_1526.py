from pathlib import Path
s=Path(__file__).parent
t=(s/'anthropic-peaked-integrality-depth-1498/S_ModularForm_qExpansion_slash_coeff_mem_of_peaked_auxiliary.lean.txt').read_text(encoding='utf-8')
start=t.index('  let X : ModularForm',t.index('theorem solution'))
end=t.index('  obtain ⟨E, P, hP, hP1⟩',start)
body=t[start:end]
body=body.replace('ModularForm.exists_levelOne_coe_eq_sum_slash','exists_levelOne_trace')
start=body.index('  have hXT₀');end=body.index('  have hFp',start)
body=body[:start]+'''  have hFAeq : FA = Translates.trSum (⇑X : ℍ → ℂ) h₀ :=
    translation_sum_eq _ _ _
  have hFAp : Function.Periodic (FA ∘ ofComplex) (1 : ℝ) := by
    rw [hFAeq]
    exact Translates.periodic_trSum (periodic_of_pm_mem X hev h₀ hT₀)
'''+body[end:]
body=body.replace('coeff_qExpansion_one_sum_slash_T_pow h hh hT hev', 'coeff_qExpansion_one_sum_slash_T_pow h hh hev')
start=body.index('  have hS0 :');end=body.index('  have hCO :',start)
body=body[:start]+body[end:]
body=body.replace('UpperHalfPlane.qExpansion_coeff_eq_zero_of_isBigO_exp_neg', 'qExpansion_coeff_zero_of_exponential_decay')
f=s/'SourceIntegralTraceDecomposition1526a.lean';assert not f.exists()
f.write_text('''import SourceIntegralTraceTranslationAssembly1524a
import SourceIntegralTraceAnalyticProducts1522a
import SourceIntegralTraceTransversalSplit1525a
import SourceTraceExponentialCoefficientVanishing1511a
import SourceIntegralTracePowerCoefficients1513a

/-! DUB-17/18 -> original Gamma1 degree preservation -> even-weight
slash integrality -> peaked auxiliary trace. Assemble the actual
level-one trace and its exact Fourier decomposition. Integral translated
coefficients and vanishing remainder coefficients are derived from the
original expansions, signed cosets and auxiliary decay. No trace identity
or Fourier vanishing is supplied as an assumption.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularForm_qExpansion_slash_coeff_mem_of_peaked_auxiliary. -/
namespace Dubon2026.SourceFunctionField.IntegralTrace
noncomputable section
open scoped MatrixGroups ModularForm Manifold
open UpperHalfPlane

theorem exists_integral_trace_decomposition
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (h : ℕ) (hh : 0 < h)
    (hT : ModularGroup.T ^ h ∈ Γ)
    (hS : ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹ ∈ Γ)
    (R : Subring ℂ) {k w : ℤ}
    (G : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    (hG : ∀ n, (qExpansion (h : ℝ) (⇑G : ℍ → ℂ)).coeff n ∈ R)
    (Θ : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) w)
    (hΘ : ∀ n, (qExpansion (h : ℝ) (⇑Θ : ℍ → ℂ)).coeff n ∈ R)
    (r h₀ m₀ : ℕ) (δ : ℝ) (hev : Even (k + (r : ℤ) * w))
    (hh₀ : 0 < h₀) (hh₀h : h₀ ∣ h)
    (hT₀ : ModularGroup.T ^ h₀ ∈ Γ ∨ -(ModularGroup.T ^ h₀) ∈ Γ)
    (hmin : ∀ j : ℕ, 0 < j → j < h₀ →
      ModularGroup.T ^ j ∉ Γ ∧ -(ModularGroup.T ^ j) ∉ Γ)
    (hdeg : ∀ j : ℤ, ModularGroup.S * ModularGroup.T ^ j ∉ Γ ∧
      -(ModularGroup.S * ModularGroup.T ^ j) ∉ Γ)
    (hdecay : ∀ β : SL(2, ℤ),
      (∀ j : ℤ, β * ModularGroup.T ^ j ∉ Γ ∧ -(β * ModularGroup.T ^ j) ∉ Γ) →
      (β * ModularGroup.S⁻¹ ∉ Γ ∧ -(β * ModularGroup.S⁻¹) ∉ Γ) →
      ((⇑Θ : ℍ → ℂ) ∣[w] (β : GL (Fin 2) ℝ)) =O[atImInfty]
        fun τ : ℍ => Real.exp (-(2 * Real.pi * ((m₀ : ℝ) + δ)) * τ.im)) :
    ∃ (F : ModularForm 𝒮ℒ (k + (r : ℤ) * w)) (A C : PowerSeries ℂ),
      qExpansion 1 (F : ℍ → ℂ) = A +
        qExpansion 1 ((⇑G : ℍ → ℂ) ∣[k] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ)) *
        qExpansion 1 ((⇑Θ : ℍ → ℂ) ∣[w] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ)) ^ r + C ∧
      (∀ i, A.coeff i ∈ R) ∧
      (∀ i : ℕ, (i : ℝ) < r * ((m₀ : ℝ) + δ) → C.coeff i = 0) := by
  classical
  obtain ⟨s, hcover, hsep, hTs, hSs, hrest⟩ :=
    exists_signed_cusp_transversal Γ hdeg h₀ hh₀ hT₀ hmin
'''+body+'''
  refine ⟨F, qExpansion 1 FA, qExpansion 1 FC, ?_, hA, hC0⟩
  rw [hqF, hSq]

end
end Dubon2026.SourceFunctionField.IntegralTrace
''',encoding='utf-8')
