from pathlib import Path
s=Path(__file__).parent
a=s/'SourceIntegralTraceSlashPeriods1523a.lean';b=s/'SourceIntegralTraceSlashPeriods1523b.lean';assert not b.exists()
b.write_text(a.read_text(encoding='utf-8').replace('convert h using 2 <;> try rfl','convert h using 2; try rfl'),encoding='utf-8');a.rename(a.with_suffix('.lean.txt'))
t=(s/'anthropic-peaked-integrality-depth-1498/S_ModularForm_qExpansion_slash_coeff_mem_of_peaked_auxiliary.lean.txt').read_text(encoding='utf-8')
prefix='''/-! DUB-17/18 -> original Gamma1 degree preservation -> even-weight
slash integrality -> peaked auxiliary trace. Exact finite translation and
signed transversal identities used by the actual trace decomposition.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularForm_qExpansion_slash_coeff_mem_of_peaked_auxiliary. -/
namespace Dubon2026.SourceFunctionField.IntegralTrace
noncomputable section
open scoped MatrixGroups ModularForm Manifold
open UpperHalfPlane GammaOne
'''
body='''
theorem translation_sum_eq (f : ℍ → ℂ) (k : ℤ) (h₀ : ℕ) :
    (fun τ : ℍ => ∑ j ∈ Finset.range h₀,
      (f ∣[k] ((ModularGroup.T ^ j : SL(2, ℤ)) : GL (Fin 2) ℝ)) τ) =
      Translates.trSum f h₀ := by
  funext τ
  exact Finset.sum_congr rfl fun j _ => slash_T_pow_apply _ _ _ _

'''
chunk=t[t.index('theorem coeff_qExpansion_one_sum_slash_T_pow'):t.index('\ntheorem sum_slash_T_pow_slash_T_eq')]
chunk=chunk.replace('    (hT : ModularGroup.T ^ h ∈ Γ) {κ : ℤ}', '    {κ : ℤ}')
start=chunk.index('  have hfun :');end=chunk.index('  congr 1\n',start)
chunk=chunk[:start]+'''  rw [translation_sum_eq, Translates.coeff_translation_sum hh₀ hper₀ hhol hbdd i]
'''+chunk[end:]
chunk=chunk.replace('UpperHalfPlane.qExpansion_coeff_mul_width (⇑X) (h₀ : ℝ) (by exact_mod_cast hh₀) hper₀ hhol hbdd\n    m\' hm\'pos (h * i)', "qExpansion_coeff_multiple_width (⇑X) (h₀ : ℝ) (by exact_mod_cast hh₀) hm'pos.ne' hper₀ hhol hbdd (h * i)")
f=s/'SourceIntegralTraceTranslationAssembly1524a.lean';assert not f.exists()
f.write_text('import SourceIntegralTraceTranslationCoefficients1518b\nimport SourceIntegralTracePeriodWidth1519b\nimport SourceIntegralTraceSlashPeriods1523b\n\n'+prefix+body+chunk+'\nend\nend Dubon2026.SourceFunctionField.IntegralTrace\n',encoding='utf-8')
body=t[t.index('theorem exists_width'):t.index('\ntheorem slash_T_zpow_apply')]
body=body.replace('pmSubgroup Γ','plusMinus Γ')
body=body.replace(':= Or.inl hT',':= (mem_plusMinus_iff Γ _).mpr (Or.inl hT)')
body=body.replace(':= hspec.2',':= (mem_plusMinus_iff Γ _).mpr hspec.2')
body=body.replace('rcases hr with hr | hr','rcases (mem_plusMinus_iff Γ _).mp hr with hr | hr')
body+='\n'+t[t.index('theorem T_pow_injective'):t.index('\nend TRMain')]
body=body.replace('theorem T_pow_injective','private theorem T_pow_injective').replace('theorem S_ne_T_pow','private theorem S_ne_T_pow')
f=s/'SourceIntegralTraceTransversalSplit1525a.lean';assert not f.exists()
f.write_text('import SourceIntegralTraceCuspTransversal1516a\n\n'+prefix+body+'\nend\nend Dubon2026.SourceFunctionField.IntegralTrace\n',encoding='utf-8')
