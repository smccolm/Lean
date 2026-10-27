from pathlib import Path
p=Path(r'E:\Lean\.tmp\dubon83')
s=(p/'fricke-cusp-descent-inputs-reuse-678/P2M/Sol/S_WLight_span_inter_rational_of_twist_stable.lean.txt').read_text(encoding='utf-8')
core=s[s.index('theorem descent_core'):s.index('theorem descent_generic')]
generic=s[s.index('theorem descent_generic'):s.index('end AbstractDescent')]
ns='Dubon2026.SourceFunctionField.TwistDescent'
imports='''import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic
'''
comment='''
/-! DUB-17/18 -> actual Gamma1 cusp realization -> rational cusp-form spanning
-> descent of the proved coefficient-twist-stable cusp image. Finite scalar
support and original-field fixed coefficients yield descent of the actual
stable subspace. Adapted from anthropics/fermats-last-theorem,
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0,
S_WLight_span_inter_rational_of_twist_stable. Only its necessary abstract
descent argument is retained; the already proved actual coefficient twist
replaces the separate external flatness/twist construction. -/
'''
for name,imp,body in [('SourceTwistDescentFiniteSupport',imports,core),('SourceTwistStableSubspaceDescent','import SourceTwistDescentFiniteSupport\n',generic)]:
 f=p/(name+'.lean');assert not f.exists();f.write_text(imp+comment+'namespace '+ns+'\nnoncomputable section\n\n'+body+'end\nend '+ns+'\n',encoding='utf-8')
print('Prepared finite-support descent and its original-subspace consumer')