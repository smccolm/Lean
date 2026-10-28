from pathlib import Path
import json,ast
p=Path(r'E:\Lean\.tmp\dubon83')
def out(n,t):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(t)
cfg=json.loads((p/'source-gamma-one-smooth-divisor-period-1-audit-config.json').read_text(encoding='utf-8'))
old='integral_image_eq_integral_abs_det_fderiv_smul';new='MeasureTheory.'+old
assert old in cfg['proofEdges'];cfg['proofEdges']=[new if n==old else n for n in cfg['proofEdges']]
out('source-gamma-one-smooth-divisor-period-1b-audit-config.json',json.dumps(cfg,indent=2)+'\n')
t=(p/'SourceGammaOneSmoothDivisorPeriodDependencyAudit1.lean').read_text(encoding='utf-8').replace(chr(96)+old,chr(96)+new)
out('SourceGammaOneSmoothDivisorPeriodDependencyAudit1b.lean',t)
t=(p/'record_source_gamma_one_smooth_divisor_period_914.py').read_text(encoding='utf-8')
t=t.replace('source-gamma-one-smooth-divisor-period-1','source-gamma-one-smooth-divisor-period-1b').replace('SourceGammaOneSmoothDivisorPeriodDependencyAudit1','SourceGammaOneSmoothDivisorPeriodDependencyAudit1b')
ast.parse(t);out('record_source_gamma_one_smooth_divisor_period_914b.py',t)
t=(p/'audit_smooth_divisor_period_914.ps1').read_text(encoding='utf-8')
t=t.replace("'SourceGammaOneSmoothDivisorPeriodAudit1',",'').replace('SourceGammaOneSmoothDivisorPeriodDependencyAudit1','SourceGammaOneSmoothDivisorPeriodDependencyAudit1b').replace('record_source_gamma_one_smooth_divisor_period_914.py','record_source_gamma_one_smooth_divisor_period_914b.py')
out('audit_smooth_divisor_period_914b.ps1',t)
out('smooth-divisor-period-audit-namespace-correction-914b.json',json.dumps(dict(reason='The native Jacobian theorem is owned by namespace MeasureTheory. Correct the fully qualified required dependency Name; retain the passed exhaustive public audit and all failed dependency evidence. No mathematics, dependency traversal or required obligation changed.',old=old,new=new),indent=2)+'\n')
print('Fresh dependency-audit successor uses exact native declaration name; passed public audit reused.')
