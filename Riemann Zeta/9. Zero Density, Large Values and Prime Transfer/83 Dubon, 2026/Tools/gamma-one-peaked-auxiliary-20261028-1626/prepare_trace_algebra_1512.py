from pathlib import Path
s=Path(__file__).parent
t=(s/'anthropic-peaked-integrality-depth-1498/S_ModularForm_qExpansion_slash_coeff_mem_of_peaked_auxiliary.lean.txt').read_text(encoding='utf-8')
prefix='''/-! DUB-17/18 -> original Gamma1 degree preservation -> even-weight
slash integrality -> peaked auxiliary trace. These are the exact numerical
and coefficient prerequisites used to isolate one slash coefficient from
the trace. Adapted from anthropics/fermats-last-theorem, Apache-2.0,
revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularForm_qExpansion_slash_coeff_mem_of_peaked_auxiliary. -/
namespace Dubon2026.SourceFunctionField.IntegralTrace
'''
body=t[t.index('theorem exists_four_mul_add_six_mul'):t.index('\nopen Filter Asymptotics')]
body=body.replace('theorem exists_four_mul_add_six_mul','private theorem exists_four_mul_add_six_mul').replace('theorem exists_params','theorem exists_trace_parameters')
f=s/'SourceIntegralTraceParameters1512a.lean';assert not f.exists()
f.write_text('import Mathlib.Tactic\n\n'+prefix+body+'\nend Dubon2026.SourceFunctionField.IntegralTrace\n',encoding='utf-8')
body=t[t.index('theorem coeff_pow_eq_zero_of_lt'):t.index('\ntheorem isBigO_mul_pow_exp')]
body+='\n'+t[t.index('theorem coeff_mul_mem'):t.index('\ntheorem slash_T_pow_eq_of_mem_or_neg_mem')]
f=s/'SourceIntegralTracePowerCoefficients1513a.lean';assert not f.exists()
f.write_text('import Mathlib.RingTheory.PowerSeries.Basic\nimport Mathlib.Analysis.Complex.Basic\nimport Mathlib.Tactic\n\n'+prefix+body+'\nend Dubon2026.SourceFunctionField.IntegralTrace\n',encoding='utf-8')
