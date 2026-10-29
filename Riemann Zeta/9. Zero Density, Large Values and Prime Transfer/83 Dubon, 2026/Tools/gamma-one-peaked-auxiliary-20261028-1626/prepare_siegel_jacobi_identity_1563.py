from pathlib import Path
import re
s=Path(__file__).parent
t=(s/'anthropic-siegel-dependencies-1553/S_jacobiTheta_two_eq_tprod.lean.txt').read_text(encoding='utf-8')
ns='Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.JacobiProduct'
body=t[t.index('variable (τ : ℂ)'):t.index('\nend JTPDEngine')]
body=re.sub(r'^p2m_reactivate[^\n]*\n','',body,flags=re.M)
a=body.index('private lemma Q_ne_zero');b=body.index('private lemma norm_q_lt_one',a);body=body[:a]+body[b:]
a=body.index('private lemma summable_Q_pow');b=body.index('private lemma summable_q_odd_mul',a);body=body[:a]+body[b:]
a=body.index('private lemma multipliable_Eu');b=body.index('private lemma multipliable_Pplus',a)
body=body[:a]+'''private lemma multipliable_Eu (hτ : 0 < τ.im) :
    Multipliable (fun n : ℕ => 1 - Q τ ^ (n + 1)) :=
  ModularForm.multipliable_one_sub_pow (norm_Q_lt_one τ hτ)

'''+body[b:]
a=body.index('section Indicator');b=body.index('section Assembly',a);body=body[:a]+body[b:]
outer=t[t.index('theorem solution (z τ : ℂ)'):t.index('\nend R3')]
outer=outer.replace('theorem solution','theorem jacobiTheta_two_eq_tprod').replace('JTPTannery.','').replace('JTPEngine.','')
f=s/'SourceSiegelJacobiProductIdentity1563a.lean';assert not f.exists()
f.write_text('''import SourceSiegelJacobiFiniteIdentity1559a
import SourceSiegelJacobiRangeLimit1562a

/-! DUB-17/18 -> original Gamma1 degree/genus preservation -> level-power
slash integrality -> actual peaked auxiliary -> Siegel holomorphy and
SL2 transformation. Assemble the actual Jacobi theta triple product from
the proved finite Gaussian identity, native theta-series summability and
the proved dominated limit. The identity uses Mathlib's original theta
function and the literal infinite product, without an equality premise.
Native eta-product convergence replaces the duplicated source proof;
unused source helper facts are omitted.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_jacobiTheta_two_eq_tprod. -/
namespace '''+ns+'''
noncomputable section
open scoped Real
open Complex Finset Filter Topology

'''+body+'\n\n'+outer+'\nend\nend '+ns+'\n',encoding='utf-8')
