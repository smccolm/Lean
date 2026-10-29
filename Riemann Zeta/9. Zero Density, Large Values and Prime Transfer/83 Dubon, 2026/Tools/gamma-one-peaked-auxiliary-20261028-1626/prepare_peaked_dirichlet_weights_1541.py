from pathlib import Path
s=Path(__file__).parent
t=(s/'anthropic-peaked-leaves-1535/S_ModularCurve_SiegelUnit_mem_span_levelBernoulliWeight_dilate_iff_even.lean.txt').read_text(encoding='utf-8')
prefix='''/-! DUB-17/18 -> original Gamma1 degree preservation -> level-power
slash integrality -> actual even-weight peaked auxiliary form -> finite
Bernoulli-order separation. Residue-class reciprocal-square weights are
diagonalized by the actual Dirichlet characters. Native character
orthogonality and nonvanishing of L(2,chi) discharge the finite convolution
kernel; no new analytic-continuation or nonvanishing hypothesis is used.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_SiegelUnit_mem_span_levelBernoulliWeight_dilate_iff_even.
No upstream resource-limit option is adopted. -/
namespace Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.Bernoulli
open Finset Real
open scoped Real
variable {N : ℕ} [NeZero N]
'''
body=t[t.index('noncomputable def Zres'):t.index('theorem eq_zero_of_forall_sum_char_inv_mul_eq_zero')]
# The final open Complex in belongs to the next theorem, not this module.
body=body.rsplit('open Complex in',1)[0]
body=body.replace('noncomputable def Zres','/-- The convergent reciprocal-square sum over one actual residue class. -/\nnoncomputable def Zres',1)
f=s/'SourcePeakedBernoulliResidueWeights1541a.lean';assert not f.exists()
f.write_text('''import SourcePeakedBernoulliMoments1540a
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Analysis.SumOverResidueClass

'''+prefix+body+'\nend Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.Bernoulli\n',encoding='utf-8')
body=t[t.index('theorem eq_zero_of_forall_sum_char_inv_mul_eq_zero'):t.index('theorem eq_zero_of_convolution')]
body=body.rsplit('open Complex in',1)[0]
f=s/'SourcePeakedBernoulliCharacterInversion1542a.lean';assert not f.exists()
f.write_text('''import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Tactic

'''+prefix+'open Complex\n\n'+body+'\nend Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.Bernoulli\n',encoding='utf-8')
body=t[t.index('theorem eq_zero_of_convolution'):t.index('\nend Ws47.BSpan',t.index('theorem eq_zero_of_convolution'))]
f=s/'SourcePeakedBernoulliConvolution1543a.lean';assert not f.exists()
f.write_text('''import SourcePeakedBernoulliResidueWeights1541a
import SourcePeakedBernoulliCharacterInversion1542a

'''+prefix+'open Complex\n\n'+body+'\nend Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.Bernoulli\n',encoding='utf-8')
