from pathlib import Path
import json,re,ast
p=Path(r'E:\Lean\.tmp\dubon83')
cfg=json.loads((p/'source-gamma-one-smooth-divisor-1-audit-config.json').read_text(encoding='utf-8'))
n='Dubon2026.SourceSmoothDivisor.finiteStabilizer'
cfg['constructions'].remove(n);cfg['theorems'].append(n)
def out(n,s):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(s)
out('source-gamma-one-smooth-divisor-1b-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda xs:'#['+', '.join(chr(96)+n for n in xs)+']'
t=(p/'SourceGammaOneSmoothDivisorAudit1.lean').read_text(encoding='utf-8')
for k in ['theorems','constructions']:
 t=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(cfg[k]),t)
out('SourceGammaOneSmoothDivisorAudit1b.lean',t)
for a,b in [('SourceGammaOneSmoothDivisorDependencyAudit1.lean','SourceGammaOneSmoothDivisorDependencyAudit1b.lean'),('SourceGammaOneSmoothDivisorScratchOwnership909.lean','SourceGammaOneSmoothDivisorScratchOwnership909b.lean')]:
 out(b,(p/a).read_text(encoding='utf-8'))
t=(p/'record_source_gamma_one_smooth_divisor_909.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-smooth-divisor-1','source-gamma-one-smooth-divisor-1b'),('SourceGammaOneSmoothDivisorAudit1','SourceGammaOneSmoothDivisorAudit1b'),('SourceGammaOneSmoothDivisorDependencyAudit1','SourceGammaOneSmoothDivisorDependencyAudit1b')]:t=t.replace(a,b)
ast.parse(t);out('record_source_gamma_one_smooth_divisor_909b.py',t)
t=(p/'audit_smooth_divisor_909.ps1').read_text(encoding='utf-8')
for a,b in [('SourceGammaOneSmoothDivisorAudit1','SourceGammaOneSmoothDivisorAudit1b'),('SourceGammaOneSmoothDivisorDependencyAudit1','SourceGammaOneSmoothDivisorDependencyAudit1b'),('SourceGammaOneSmoothDivisorScratchOwnership909','SourceGammaOneSmoothDivisorScratchOwnership909b'),('record_source_gamma_one_smooth_divisor_909.py','record_source_gamma_one_smooth_divisor_909b.py')]:t=t.replace(a,b)
out('audit_smooth_divisor_909b.ps1',t)
out('smooth-divisor-audit-kind-correction-909b.json',json.dumps(dict(reason='Lean compiles the Prop-valued Finite instance as a theorem, so classify finiteStabilizer in theorem registrations. All original audit logs retained. No mathematical source or audit standard changed.',theorems=len(cfg['theorems']),constructions=len(cfg['constructions']),queries=len(cfg['queries'])),indent=2)+'\n')
print('Corrected registration kind; fresh successor audits, config, recorder and runner.')
