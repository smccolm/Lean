from pathlib import Path
import re
s=Path(__file__).parent
ns='Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary'
t=(s/'anthropic-peaked-core-1533/S_ModularCurve_SiegelUnit_exists_peaked_exponent.lean.txt').read_text(encoding='utf-8')
body=t[t.index('theorem W_zero '):t.index('\nend sums')]
body=re.sub(r'\bW\b','Bernoulli.wt',body)
body=body[:body.index('theorem sum_W_add_mul_le ')] + '''theorem sum_W_add_mul_le (x y : ZMod N) :
    ∑ s : ZMod N, Bernoulli.wt N (x + s * y).val ≤ (N : ℤ) ^ 3 := by
  calc
    _ ≤ ∑ _s : ZMod N, (N : ℤ) ^ 2 :=
      Finset.sum_le_sum fun s _ => W_le_sq (ZMod.val_lt (x + s * y)).le
    _ = (N : ℤ) ^ 3 := by simp [pow_succ, mul_comm]
'''
body=body.replace('ModularCurve.SiegelUnit.sum_levelBernoulliWeight_add_mul', 'Bernoulli.Distribution.sum_zmod_Bt')
body=body.replace('simpa [Bernoulli.wt] using h','simpa [Bernoulli.wt, Bernoulli.Distribution.Bt] using h')
construction=t[t.index('def wt (N : ℕ) (r : ZMod N)'):t.index('\nend construction')]
construction=re.sub(r'\bwt\b','residueWeight',construction)
construction=construction.replace('def residueWeight ', '/-- The positive totient weight for the Bernoulli mean constraint. -/\ndef residueWeight ',1)
f=s/'SourcePeakedExponentHelpers1549a.lean';assert not f.exists()
f.write_text('''import SourcePeakedBernoulliProgressions1547a

/-! DUB-17/18 -> original Gamma1 degree preservation -> level-power
slash integrality -> actual even-weight peaked auxiliary -> integer
exponent construction. These are the precise finite sum and size bounds
used by that construction. The uniform affine-sum bound is proved
directly from the pointwise quadratic bound, avoiding the longer source
gcd argument. The normalized Bernoulli polynomial is reused unchanged.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_SiegelUnit_exists_peaked_exponent. -/
namespace '''+ns+'''.Exponents
open Finset

'''+body+'\nend sums\n\nsection construction\nvariable {N : ℕ} [NeZero N]\n\n'+construction+'\nend construction\nend '+ns+'.Exponents\n',encoding='utf-8')
