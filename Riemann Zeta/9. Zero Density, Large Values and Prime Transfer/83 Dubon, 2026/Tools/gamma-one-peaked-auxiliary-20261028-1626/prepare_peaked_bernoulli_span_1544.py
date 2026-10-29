from pathlib import Path
s=Path(__file__).parent
a=s/'SourcePeakedBernoulliCharacterInversion1542a.lean';b=s/'SourcePeakedBernoulliCharacterInversion1542b.lean';assert not b.exists()
t=a.read_text(encoding='utf-8').replace('import Mathlib.Tactic','import Mathlib.Analysis.Complex.Polynomial.Basic\nimport Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed\nimport Mathlib.Tactic',1)
b.write_text(t,encoding='utf-8');a.rename(a.with_suffix('.lean.txt'))
f=s/'SourcePeakedBernoulliConvolution1543a.lean';assert not f.with_suffix('.log').exists()
f.write_text(f.read_text(encoding='utf-8').replace('import SourcePeakedBernoulliCharacterInversion1542a','import SourcePeakedBernoulliCharacterInversion1542b'),encoding='utf-8')
t=(s/'anthropic-peaked-leaves-1535/S_ModularCurve_SiegelUnit_mem_span_levelBernoulliWeight_dilate_iff_even.lean.txt').read_text(encoding='utf-8')
prefix='''/-! DUB-17/18 -> original Gamma1 degree preservation -> level-power
slash integrality -> actual even-weight peaked auxiliary form -> finite
Bernoulli-order separation. The actual Bernoulli dilates span exactly
the even rational functions on the residue ring. The kernel argument
uses the proved Dirichlet convolution calculation and native finite
Fourier inversion, followed by finite-dimensional linear algebra.
No spanning or separating-exponent hypothesis is assumed.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_SiegelUnit_mem_span_levelBernoulliWeight_dilate_iff_even.
No upstream resource-limit option is adopted. -/
namespace Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.Bernoulli
open Finset Real
open scoped Real
'''
body=t[t.index('theorem psi_eq_zero'):t.index('\nend D')]
f=s/'SourcePeakedBernoulliVanishing1544a.lean';assert not f.exists()
f.write_text('import SourcePeakedBernoulliConvolution1543a\n\n'+prefix+'variable {N : ℕ} [NeZero N]\n\n'+body+'\nend Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.Bernoulli\n',encoding='utf-8')
body=t[t.index('noncomputable def sinZ'):t.index('\nend E')]
body=body.replace('noncomputable def sinZ','/-- The sine component of the standard residue-ring additive phase. -/\nnoncomputable def sinZ',1)
f=s/'SourcePeakedBernoulliFourierInversion1545a.lean';assert not f.exists()
f.write_text('import SourcePeakedBernoulliMoments1540a\nimport Mathlib.Analysis.Fourier.ZMod\n\n'+prefix+'variable {N : ℕ} [NeZero N]\n\n'+body+'\nend Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.Bernoulli\n',encoding='utf-8')
body=t[t.index('section F'):t.index('\nend F')]
body=body.replace('def fam ', '/-- The actual rational Bernoulli-weight dilation family. -/\ndef fam ',1)
body=body.replace('noncomputable def T ', '/-- The linear combination map for the Bernoulli dilation family. -/\nnoncomputable def T ',1)
body=body.replace('def evenSub ', '/-- The subspace of even rational functions on the residue ring. -/\ndef evenSub ',1)
body=body.replace('noncomputable def TE ', '/-- The Bernoulli linear combination map restricted to the even subspace. -/\nnoncomputable def TE ',1)
f=s/'SourcePeakedBernoulliSpan1546a.lean';assert not f.exists()
f.write_text('import SourcePeakedBernoulliVanishing1544a\nimport SourcePeakedBernoulliFourierInversion1545a\nimport Mathlib.LinearAlgebra.FiniteDimensional.Basic\n\n'+prefix+body+'\nend F\nend Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.Bernoulli\n',encoding='utf-8')
