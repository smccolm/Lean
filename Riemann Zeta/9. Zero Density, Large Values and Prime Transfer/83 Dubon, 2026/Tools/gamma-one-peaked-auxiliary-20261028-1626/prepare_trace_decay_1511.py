from pathlib import Path
s=Path(__file__).parent
src=s/'anthropic-trace-dependencies-1510/S_UpperHalfPlane_qExpansion_coeff_eq_zero_of_isBigO_exp_neg.lean.txt'
t=src.read_text(encoding='utf-8')
body=t[t.index('open UpperHalfPlane Filter'):t.index('\nend DecayVanish')]
body=body.replace('theorem norm_integrand_le', 'private theorem norm_integrand_le').replace('theorem main ', 'theorem qExpansion_coeff_zero_of_exponential_decay ')
f=s/'SourceTraceExponentialCoefficientVanishing1511a.lean';assert not f.exists()
f.write_text('''import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.Tactic

/-! DUB-17/18 -> original Gamma1 degree preservation -> even-weight
slash integrality -> peaked auxiliary trace. Exponential decay of the
remaining cusp terms forces precisely the required initial coefficients
to vanish. Existing ModularCoefficientOrder handles modular-form classes
and integral orders; this argument applies directly to the periodic
analytic remainder and the real decay threshold required here.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_UpperHalfPlane_qExpansion_coeff_eq_zero_of_isBigO_exp_neg. -/
namespace Dubon2026.SourceFunctionField.IntegralTrace
noncomputable section
'''+body+'\nend\nend Dubon2026.SourceFunctionField.IntegralTrace\n',encoding='utf-8')
