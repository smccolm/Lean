from pathlib import Path
s = Path(__file__).parent
ns = 'Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.Bernoulli'
t = (s/'anthropic-peaked-leaves-1535/S_ModularCurve_SiegelUnit_sum_totient_mul_levelBernoulliWeight_dilate_eq_zero.lean.txt').read_text(encoding='utf-8')
body = t[t.index('def J2 '):t.index('\nend Ws18BDeg')]
body = body.replace('def J2 ', '/-- The quadratic Moebius convolution used to cancel the weighted Bernoulli mean. -/\ndef J2 ', 1)
outer = t[t.index('theorem solution '):].replace('theorem solution ', 'theorem sum_totient_mul_weight_dilate_eq_zero ', 1)
f = s/'SourcePeakedBernoulliTotient1548a.lean'
assert not f.exists()
f.write_text('''import SourcePeakedBernoulliProgressions1547a
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Totient

/-! DUB-17/18 -> original Gamma1 degree preservation -> level-power
slash integrality -> actual even-weight peaked auxiliary -> nonnegative
integer exponents. The weighted Bernoulli mean vanishes for nonzero
dilates. This forces the zero coefficient of the separating profile to
vanish, which is necessary to exclude the undefined Siegel factor (0,0).
The proof reuses Mathlib Moebius inversion and the already proved exact
residue progression identity; no separate distribution proof is copied.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_SiegelUnit_sum_totient_mul_levelBernoulliWeight_dilate_eq_zero. -/
namespace '''+ns+'''.Totient
open Finset
open '''+ns+'''.Distribution

'''+body+'\n\n'+outer+'\nend '+ns+'.Totient\n',encoding='utf-8')
