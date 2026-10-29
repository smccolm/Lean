from pathlib import Path
s=Path(__file__).parent
a=s/'SourcePeakedBernoulliFourier1539a.lean';b=s/'SourcePeakedBernoulliFourier1539b.lean';assert not b.exists()
t=a.read_text(encoding='utf-8').replace('  convert h using 1\n  · rfl\n  rw [wt_cast]', '  convert h using 1\n  rw [wt_cast]')
b.write_text(t,encoding='utf-8');a.rename(a.with_suffix('.lean.txt'))
t=(s/'anthropic-peaked-leaves-1535/S_ModularCurve_SiegelUnit_mem_span_levelBernoulliWeight_dilate_iff_even.lean.txt').read_text(encoding='utf-8')
body=t[t.index('noncomputable def psi'):t.index('\nnoncomputable def Zres')]
body=body.replace('noncomputable def psi','/-- The cosine moment of a function on the actual residue ring. -/\nnoncomputable def psi',1)
f=s/'SourcePeakedBernoulliMoments1540a.lean';assert not f.exists()
f.write_text('''import SourcePeakedBernoulliFourier1539b

/-! DUB-17/18 -> original Gamma1 degree preservation -> level-power
slash integrality -> actual even-weight peaked auxiliary existence ->
Bernoulli-order separation. Orthogonality to the literal Bernoulli
weights forces the corresponding convergent cosine-moment sums to
vanish. Reuses the proved Bernoulli Fourier series; no separating
exponent or auxiliary existence premise is introduced.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_SiegelUnit_mem_span_levelBernoulliWeight_dilate_iff_even.
No upstream resource-limit option is adopted. -/
namespace Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.Bernoulli
open Finset Real
open scoped Real
variable {N : ℕ} [NeZero N]

'''+body+'\nend Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.Bernoulli\n',encoding='utf-8')
