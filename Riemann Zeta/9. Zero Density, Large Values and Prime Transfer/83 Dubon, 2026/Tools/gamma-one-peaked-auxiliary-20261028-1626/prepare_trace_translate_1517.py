from pathlib import Path
s=Path(__file__).parent
t=(s/'anthropic-trace-dependencies-1510/S_UpperHalfPlane_qExpansion_coeff_sum_vAdd_eq_mul_coeff.lean.txt').read_text(encoding='utf-8')
prefix='''/-! DUB-17/18 -> original Gamma1 degree preservation -> even-weight
slash integrality -> peaked auxiliary trace. The finite translation sum
is periodic of width one and has the required holomorphic, bounded and
Fourier properties. Reuse the native period-power identity, avoiding the
upstream bespoke function wrapper. Adapted from
anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_UpperHalfPlane_qExpansion_coeff_sum_vAdd_eq_mul_coeff. -/
namespace Dubon2026.SourceFunctionField.IntegralTrace.Translates
noncomputable section
open UpperHalfPlane Filter Function Complex Function.Complex
open scoped Real Topology Manifold
'''
body=t[t.index('variable (f : ℍ'):t.index('\ntheorem qParam_vadd')]
body=body.replace('theorem vadd_eq_ofComplex','private theorem vadd_eq_ofComplex').replace('theorem translate_comp_ofComplex','private theorem translate_comp_ofComplex').replace('theorem trSum_comp_ofComplex_of_im_pos','private theorem trSum_comp_ofComplex_of_im_pos')
f=s/'SourceIntegralTraceTranslates1517a.lean';assert not f.exists()
f.write_text('import Dubon2026.SourceQExpansionPeriodWidth\nimport Mathlib.Tactic\n\n'+prefix+body+'\nend\nend Dubon2026.SourceFunctionField.IntegralTrace.Translates\n',encoding='utf-8')
body=t[t.index('theorem qParam_vadd'):t.index('\nend ProjTranslates')]
body=body.replace('theorem qParam_vadd','private theorem qParam_vadd').replace('theorem sum_exp_eq','private theorem sum_exp_eq')
start=body.index('theorem qParam_pow_h₀');end=body.index('theorem main',start)
body=body[:start]+body[end:]
body=body.replace('theorem main','theorem coeff_translation_sum')
body=body.replace('qParam_pow_h₀ hh₀', '← SourceFricke.qParam_one_eq_pow hh₀.ne\'')
body=body.replace('  let F : FnWrap := ⟨trSum f h₀⟩', '  let F : C(ℍ, ℂ) := ⟨trSum f h₀, (mdifferentiable_trSum hhol).continuous⟩')
f=s/'SourceIntegralTraceTranslationCoefficients1518a.lean';assert not f.exists()
f.write_text('import SourceIntegralTraceTranslates1517a\n\n'+prefix+'variable {f : ℍ → ℂ} {h₀ : ℕ}\n\n'+body+'\nend\nend Dubon2026.SourceFunctionField.IntegralTrace.Translates\n',encoding='utf-8')
# One remaining exact source file: arbitrary positive width multiplication.
a=s/'fetch_trace_dependencies_1510.py';b=s/'fetch_trace_width_dependency_1517.py';assert not b.exists()
tx=a.read_text(encoding='utf-8');start=tx.index('names=');end=tx.index('\nknown=',start)
tx=tx[:start]+"names=['S_UpperHalfPlane_qExpansion_coeff_mul_width']"+tx[end:]
b.write_text(tx.replace('anthropic-trace-dependencies-1510','anthropic-trace-width-1517'),encoding='utf-8')
