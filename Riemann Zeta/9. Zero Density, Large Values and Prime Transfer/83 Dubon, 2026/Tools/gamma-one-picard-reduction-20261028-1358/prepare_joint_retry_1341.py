from pathlib import Path
s=Path(r'E:\Lean\.tmp\dubon83')
p=s/'SourceJointSeparableConstants1340a.lean'
t=p.read_text(encoding='utf-8').replace('SourceFunctionField.GaussReduction.algebraicClosure_rat_valuation_krullDimLE_one','algebraicClosure_rat_valuation_krullDimLE_one')
(s/'SourceJointSeparableConstants1340b.lean').write_text(t,encoding='utf-8')
p.rename(p.with_suffix('.lean.txt'))
p=s/'SourceGammaOneJointChartDimension1337c.lean'
p.rename(p.with_suffix('.lean.txt'))
