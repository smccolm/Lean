from pathlib import Path
s=Path(__file__).parent
ns='Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary'
def write(n,c):
 f=s/n;assert not f.exists();f.write_text(c,encoding='utf-8')
header='''/-! DUB-17/18 -> original Gamma1 degree/genus preservation -> level-power
slash integrality -> actual peaked auxiliary. Use the literal Siegel
infinite product and identify it with the original analytic Jacobi theta
function divided by the native nonvanishing eta product. This discharges
holomorphy of the required factors and supplies common identities for
their SL2 transformation; modularity and integral expansions remain
separate obligations. No abstract function replaces the product.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
Def_ModularCurve_SiegelFunction and
S_ModularCurve_SiegelUnit_differentiableOn_siegelFun. -/
'''
t=(s/'anthropic-peaked-leaves-1535/Def_ModularCurve_SiegelFunction.lean.txt').read_text(encoding='utf-8')
body=t[t.index('def siegelFun '):t.index('\nend ModularCurve')]
body=body.replace('def siegelFun ', '/-- The source Siegel function, defined by its literal exponential infinite product. -/\ndef siegelFun ',1)
write('SourceSiegelFunction1564a.lean','''import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

'''+header+'namespace '+ns+'\nnoncomputable section\n\n'+body+'\nend\nend '+ns+'\n')
t=(s/'anthropic-peaked-leaves-1535/S_ModularCurve_SiegelUnit_differentiableOn_siegelFun.lean.txt').read_text(encoding='utf-8')
t=t.replace('ModularCurve.siegelFun','siegelFun')
intro='namespace '+ns+'.Siegel\nnoncomputable section\nopen Complex\nopen UpperHalfPlane hiding I\nopen scoped Manifold Real MatrixGroups\n\n'
ending='\nend\nend '+ns+'.Siegel\n'
body=t[t.index('def qq '):t.index('def w (N : ℕ)')]
docs={'qq':'The original upper-half-plane exponential parameter.', 'qa':'The actual torsion exponential phase in the Siegel product.', 'pref':'The source exponential normalization of the Siegel product.', 'sprod':'The literal product factors after the source exponential normalization.', 'P':'The actual Euler product in the native eta function.'}
for name,doc in docs.items():body=body.replace('def '+name+' ', '/-- '+doc+' -/\ndef '+name+' ',1)
write('SourceSiegelProductCore1565a.lean','import SourceSiegelFunction1564a\nimport Mathlib.NumberTheory.ModularForms.DedekindEta\nimport Mathlib.Tactic\n\n'+header+intro+body+ending)
body=t[t.index('def w (N : ℕ)'):t.index('theorem differentiable_w ')]
body=body.replace('def w ', '/-- The affine theta argument identifying the original Siegel product. -/\ndef w ',1)
body=body.replace('rw [jacobiTheta_two_eq_tprod','rw [JacobiProduct.jacobiTheta_two_eq_tprod')
write('SourceSiegelThetaIdentification1566a.lean','import SourceSiegelProductCore1565a\nimport SourceSiegelJacobiProductIdentity1563a\n\n'+header+intro+body+ending)
body=t[t.index('theorem differentiable_w '):t.index('\nend E97cSHol')]
write('SourceSiegelHolomorphic1567a.lean','import SourceSiegelThetaIdentification1566a\n\n'+header+intro+body+ending)
