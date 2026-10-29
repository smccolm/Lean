from pathlib import Path
s=Path(__file__).parent
t=(s/'anthropic-peaked-leaves-1535/S_ModularCurve_SiegelUnit_sum_levelBernoulliWeight_add_mul.lean.txt').read_text(encoding='utf-8')
body=t[t.index('def Bt '):t.index('\nend Ws18BDist')]
body=body.replace('def Bt ', '/-- The same integer-normalized Bernoulli weight with integer arguments for residue progressions. -/\ndef Bt ',1)
f=s/'SourcePeakedBernoulliProgressions1547a.lean';assert not f.exists()
f.write_text('''import SourcePeakedBernoulliFourier1539b

/-! DUB-17/18 -> original Gamma1 degree preservation -> level-power
slash integrality -> actual even-weight peaked auxiliary form -> source
nonnegative exponent construction. Compute the exact Bernoulli-weight
sum along each affine residue progression, including nonunit steps, by
the native ZMod representation and gcd identities. This is the finite
distribution identity required by the source cusp-order calculation.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_SiegelUnit_sum_levelBernoulliWeight_add_mul. -/
namespace Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.Bernoulli.Distribution
open Finset

'''+body+'\nend Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.Bernoulli.Distribution\n',encoding='utf-8')
