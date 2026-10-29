from pathlib import Path
s=Path(__file__).parent
t=(s/'anthropic-siegel-dependencies-1553/S_ModularCurve_siegelFun_specialLinearGroup_smul.lean.txt').read_text(encoding='utf-8').replace('ModularCurve.siegelFun','siegelFun')
ns='Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.Siegel'
intro='namespace '+ns+'\nnoncomputable section\nopen Complex\nopen UpperHalfPlane hiding I\nopen scoped Real MatrixGroups\n\n'
ending='\nend\nend '+ns+'\n'
header='''/-! DUB-17/18 -> original Gamma1 degree/genus preservation -> level-power
slash integrality -> peaked auxiliary existence -> the actual Siegel
product transformation. Reuse the proved literal product/theta equality,
native theta and eta transformations, and native generators of SL(2,Z).
The twelfth-root multiplier is derived from the generator identities;
no slash-invariance or multiplier-existence hypothesis is supplied.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_siegelFun_specialLinearGroup_smul. -/
'''
parts=[('SourceSiegelEtaTransform1568a','import SourceSiegelThetaIdentification1566a\nimport Mathlib.NumberTheory.ModularForms.Discriminant\n','theorem sqrt_bridge ','theorem theta_S '),
 ('SourceSiegelThetaTransform1569a','import SourceSiegelEtaTransform1568a\n','theorem theta_S ','theorem sprod_S '),
 ('SourceSiegelInversion1570a','import SourceSiegelThetaTransform1569a\n','theorem sprod_S ','def Law '),
 ('SourceSiegelSL2Transformation1571a','import SourceSiegelInversion1570a\n','def Law ','\nend SiegelSL2')]
for m,imports,a,b in parts:
 body=t[t.index(a):t.index(b)]
 if m=='SourceSiegelSL2Transformation1571a':body=body.replace('def Law ', '/-- The literal source transformation law with a common twelfth-root multiplier. -/\ndef Law ',1)
 f=s/(m+'.lean');assert not f.exists();f.write_text(imports+'\n'+header+intro+body+ending,encoding='utf-8')
