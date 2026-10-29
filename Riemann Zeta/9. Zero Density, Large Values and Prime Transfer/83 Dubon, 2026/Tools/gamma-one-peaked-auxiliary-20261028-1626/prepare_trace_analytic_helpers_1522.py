from pathlib import Path
s=Path(__file__).parent
t=(s/'anthropic-peaked-integrality-depth-1498/S_ModularForm_qExpansion_slash_coeff_mem_of_peaked_auxiliary.lean.txt').read_text(encoding='utf-8')
prefix='''/-! DUB-17/18 -> original Gamma1 degree preservation -> even-weight
slash integrality -> peaked auxiliary trace. Exact slash-product and
analytic identities needed to form the three-part trace decomposition;
no degree, genus or coefficient-integrality conclusion is assumed.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularForm_qExpansion_slash_coeff_mem_of_peaked_auxiliary. -/
namespace Dubon2026.SourceFunctionField.IntegralTrace
noncomputable section
open scoped MatrixGroups ModularForm Manifold
open UpperHalfPlane Filter Asymptotics
'''
body=t[t.index('section G4'):t.index('\ntheorem coeff_pow_eq_zero_of_lt')]
for n in ['periodic_pow','mdifferentiable_pow','isBoundedAtImInfty_pow']:
 body=body.replace('theorem '+n,'private theorem '+n)
body+='\n'+t[t.index('theorem isBigO_mul_pow_exp'):t.index('\nsection G7')]
body+='\n'+t[t.index('theorem pow_slash_SL2'):t.index('\ntheorem T_pow_injective')]
f=s/'SourceIntegralTraceAnalyticProducts1522a.lean';assert not f.exists()
f.write_text('import SourceIntegralTraceModularForm1515a\n\n'+prefix+body+'\nend\nend Dubon2026.SourceFunctionField.IntegralTrace\n',encoding='utf-8')
body=t[t.index('theorem mdifferentiable_slash'):t.index('\nsection G4')]
body=body.replace('theorem mdifferentiable_slash {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]', 'theorem mdifferentiable_slash {Γ : Subgroup SL(2, ℤ)}')
body=body.replace('theorem denom_T_zpow','private theorem denom_T_zpow')
body+='''
theorem slash_eq_of_mem_or_neg_mem {Γ : Subgroup SL(2, ℤ)} {κ : ℤ}
    (X : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) κ) (hκ : Even κ)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Γ ∨ -γ ∈ Γ) :
    (⇑X : ℍ → ℂ) ∣[κ] (γ : GL (Fin 2) ℝ) = ⇑X := by
  rcases hγ with hγ | hγ
  · exact SlashInvariantForm.slash_action_eqn X _ (Subgroup.mem_map_of_mem _ hγ)
  · rw [← ModularForm.SL_slash, ← slash_neg_even hκ, ModularForm.SL_slash]
    exact SlashInvariantForm.slash_action_eqn X _ (Subgroup.mem_map_of_mem _ hγ)

theorem periodic_of_pm_mem {Γ : Subgroup SL(2, ℤ)} {κ : ℤ}
    (X : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) κ) (hκ : Even κ)
    (m : ℕ) (hm : ModularGroup.T ^ m ∈ Γ ∨ -(ModularGroup.T ^ m) ∈ Γ) :
    Function.Periodic ((⇑X : ℍ → ℂ) ∘ ofComplex) (m : ℝ) :=
  periodic_comp_ofComplex_of_slash_T_pow_eq _ κ m
    (slash_eq_of_mem_or_neg_mem X hκ _ hm)

'''
body+=t[t.index('theorem natCast_mem_strictPeriods'):t.index('\ntheorem coeff_mul_mem')]
f=s/'SourceIntegralTraceSlashPeriods1523a.lean';assert not f.exists()
f.write_text('import SourceIntegralTraceModularForm1515a\n\n'+prefix+body+'\nend\nend Dubon2026.SourceFunctionField.IntegralTrace\n',encoding='utf-8')
