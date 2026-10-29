from pathlib import Path
s=Path(__file__).parent
t=(s/'anthropic-siegel-dependencies-1553/S_jacobiTheta_two_eq_tprod.lean.txt').read_text(encoding='utf-8')
ns='Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.JacobiProduct'
header='''/-! DUB-17/18 -> original Gamma1 degree/genus preservation -> level-power
slash integrality -> peaked auxiliary -> Siegel-product transformation
and holomorphy -> Jacobi theta product. These are the exact convergence
bounds for the finite Gaussian approximation. Mathlib supplies the
geometric-product convergence and dominated convergence; the source
quotient bounds discharge their actual denominator hypotheses.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_jacobiTheta_two_eq_tprod. -/
'''
def write(n,c):
 f=s/n;assert not f.exists();f.write_text(c,encoding='utf-8')
body=t[t.index('theorem summable_norm_neg_pow '):t.index('theorem multipliable_one_sub_pow ')]
body+=t[t.index('theorem tendsto_qfact '):t.index('def fam (c : ℕ → ℤ → ℂ)')]
body=body.replace('(multipliable_one_sub_pow hQ)','(ModularForm.multipliable_one_sub_pow hQ)')
write('SourceSiegelJacobiProductBounds1560a.lean','''import SourceSiegelJacobiFiniteProducts1557a
import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.Analysis.SpecialFunctions.Log.Summable

'''+header+'namespace '+ns+'\nopen Finset Filter Topology\nvariable {Q : ℂ}\n\n'+body+'\nend '+ns+'\n')
body=t[t.index('def fam (c : ℕ → ℤ → ℂ)'):t.index('theorem tendsto_sum_range ')]
body=body.replace('def fam ', '/-- The actual finite Gaussian sum extended by zero outside its interval. -/\ndef fam ',1)
write('SourceSiegelJacobiDominatedLimit1561a.lean','''import SourceSiegelJacobiProductBounds1560a
import Mathlib.Analysis.Normed.Group.Tannery

'''+header+'namespace '+ns+'\nopen Finset Filter Topology\nvariable {Q : ℂ}\n\n'+body+'\nend '+ns+'\n')
body=t[t.index('theorem tendsto_sum_range '):t.index('\nend JTPTannery')]
write('SourceSiegelJacobiRangeLimit1562a.lean','import SourceSiegelJacobiDominatedLimit1561a\n\n'+header+'namespace '+ns+'\nopen Finset Filter Topology\nvariable {Q : ℂ}\n\n'+body+'\nend '+ns+'\n')
