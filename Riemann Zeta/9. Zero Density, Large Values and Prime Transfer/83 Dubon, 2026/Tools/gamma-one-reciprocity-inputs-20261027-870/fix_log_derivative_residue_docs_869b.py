from pathlib import Path
import json,shutil,re,ast
p=Path(__file__).parent
cfg=json.loads((p/'source-gamma-one-log-derivative-residues-1-audit-config.json').read_text(encoding='utf-8'))
d=p/'log-derivative-residues-lint-failed-869a';d.mkdir()
for m in cfg['modules']:
 f=p/(m+'.lean');shutil.copy2(f,d/(f.name+'.txt'))
 for ext in ['.log','.exit']:
  e=p/(cfg['compileEvidence'][m]+ext);shutil.copy2(e,d/e.name)
for n in ['SourceGammaOneLogDerivativeResiduesAudit1.lean','SourceGammaOneLogDerivativeResiduesAudit1.log','SourceGammaOneLogDerivativeResiduesAudit1.exit','source-gamma-one-log-derivative-residues-1-audit-config.json']:
 f=p/n;shutil.copy2(f,d/(n+('.txt' if f.suffix=='.lean' else '')))
changes={
 'SourceComplexDbarCutoff':[
 ('noncomputable def D ', '/-- The antiholomorphic derivative in the standard complex coordinates. -/\nnoncomputable def D '),
 ('noncomputable def φ ', '/-- Smooth real cutoff equal to one below one and zero above two. -/\nnoncomputable def φ '),
 ('noncomputable def η ', '/-- Radial compact cutoff about the pole, at the actual positive scale. -/\nnoncomputable def η ')],
 'SourceComplexResidueLocalModels':[
 ('noncomputable def Freg ', '/-- The finite part after subtracting the prescribed simple pole at each center. -/\nnoncomputable def Freg ')]
}
strip=lambda t:re.sub(r'/\-.*?\-/','',t,flags=re.S).split()
for m,repls in changes.items():
 f=p/(m+'.lean');old=f.read_text(encoding='utf-8');t=old
 for a,b in repls:assert t.count(a)==1;t=t.replace(a,b)
 assert strip(old)==strip(t)
 f.write_text(t,encoding='utf-8',newline='\n')
for m in cfg['modules'][1:]:cfg['compileEvidence'][m]=m+'869b'
def out(n,t):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(t)
out('source-gamma-one-log-derivative-residues-1b-audit-config.json',json.dumps(cfg,indent=2)+'\n')
out('SourceGammaOneLogDerivativeResiduesAudit1b.lean',(p/'SourceGammaOneLogDerivativeResiduesAudit1.lean').read_text(encoding='utf-8-sig'))
t=(p/'record_source_gamma_one_log_derivative_residues_869.py').read_text(encoding='utf-8')
t=t.replace('source-gamma-one-log-derivative-residues-1','source-gamma-one-log-derivative-residues-1b').replace("SourceGammaOneLogDerivativeResiduesAudit1.log","SourceGammaOneLogDerivativeResiduesAudit1b.log")
ast.parse(t);out('record_source_gamma_one_log_derivative_residues_869b.py',t)
out('log-derivative-residues-doc-review-869b.json',json.dumps(dict(reason='Strict docBlame audit found four undocumented constructions. Added only documentation strings; all mathematical tokens identical. Failed audit, sources and successful compile evidence preserved.',changed=list(changes),failedAudit='SourceGammaOneLogDerivativeResiduesAudit1.log',successorAudit='SourceGammaOneLogDerivativeResiduesAudit1b.lean'),indent=2)+'\n')
print('Prepared documentation-only repair and fresh successor audit; failed evidence preserved.')
