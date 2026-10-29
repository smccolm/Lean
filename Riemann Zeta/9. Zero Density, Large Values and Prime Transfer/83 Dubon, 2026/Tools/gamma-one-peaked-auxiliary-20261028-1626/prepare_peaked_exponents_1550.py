from pathlib import Path
import re
s=Path(__file__).parent
ns='Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary'
old=s/'SourcePeakedExponentHelpers1549a.lean'
assert not old.with_suffix('.lean.txt').exists()
t=old.read_text(encoding='utf-8').replace('Int.emod_one, mul_zero, zero_mul, sub_zero','Int.emod_one, mul_zero, sub_zero')
old.rename(old.with_suffix('.lean.txt'))
f=s/'SourcePeakedExponentHelpers1549b.lean';assert not f.exists()
f.write_text(t,encoding='utf-8')
t=(s/'anthropic-peaked-core-1533/S_ModularCurve_SiegelUnit_exists_peaked_exponent.lean.txt').read_text(encoding='utf-8')
body=t[t.index('theorem solution '):].replace('theorem solution ', 'theorem exists_peaked_exponent ',1)
body=re.sub(r'\bW\b','Bernoulli.wt',body)
body=re.sub(r'(?<!\.)\bwt\b','residueWeight',body)
body=body.replace('ModularCurve.SiegelUnit.mem_span_levelBernoulliWeight_dilate_iff_even N T','Bernoulli.mem_span_iff_even T')
body=body.replace('ModularCurve.SiegelUnit.sum_totient_mul_levelBernoulliWeight_dilate_eq_zero','Bernoulli.Totient.sum_totient_mul_weight_dilate_eq_zero')
body=body.replace('smul_eq_mul, Bernoulli.wt] using this','smul_eq_mul, Bernoulli.fam, Bernoulli.wt] using this')
f=s/'SourcePeakedExponents1550a.lean';assert not f.exists()
f.write_text('''import SourcePeakedBernoulliSpan1546a
import SourcePeakedBernoulliTotient1548a
import SourcePeakedExponentHelpers1549b

/-! DUB-17/18 -> original Gamma1 degree preservation -> level-power
slash integrality -> actual even-weight peaked auxiliary form. This
constructs the actual nonnegative integer exponent family and its
literal Bernoulli cusp orders, proves translation invariance, excludes
the zero Siegel factor, and proves the required strict separation on
primitive columns outside the two exceptional signed cusp classes.
Finite spanning, weighted-mean cancellation and denominator clearing
are proved inputs, not exponent-existence hypotheses. Analytic Siegel
products and their arithmetic expansions remain separate obligations.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_SiegelUnit_exists_peaked_exponent. -/
namespace '''+ns+'''.Exponents
open Finset

'''+body+'\nend '+ns+'.Exponents\n',encoding='utf-8')
