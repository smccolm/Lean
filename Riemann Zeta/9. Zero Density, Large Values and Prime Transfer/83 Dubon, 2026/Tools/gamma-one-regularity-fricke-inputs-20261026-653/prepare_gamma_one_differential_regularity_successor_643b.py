from pathlib import Path
import json,ast,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
old=p/'SourceGammaOneDifferentialRegularityDependencyAudit6.lean'
s=old.read_text(encoding='utf-8')
assert s.count('\\n')==3
new=p/'SourceGammaOneDifferentialRegularityDependencyAudit6b.lean';assert not new.exists()
new.write_text(s.replace('\\n','\n'),encoding='utf-8')
cfg=p/'source-gamma-one-differential-regularity-6b-audit-config.json';assert not cfg.exists()
cfg.write_bytes((p/'source-gamma-one-differential-regularity-6-audit-config.json').read_bytes())
rd=json.loads((p/'gamma1-differential-regularity-route-643.json').read_text(encoding='utf-8'))
rd['auditSuccessor']=dict(reason='The first generated declaration-value audit contained literal backslash-n sequences after its final log message. Its source/log/exit are preserved. Fresh audit 6b repairs only the generator output separators; mathematical modules and the successful exhaustive audit are unchanged and not rerun.',failed=[dict(path=str(old.with_suffix(e)),sha256=sha(old.with_suffix(e))) for e in ['.lean','.log','.exit']],successfulExhaustive=dict(path=str(p/'SourceGammaOneDifferentialRegularityAudit6.log'),sha256=sha(p/'SourceGammaOneDifferentialRegularityAudit6.log')),successor=dict(path=str(new),sha256=sha(new)))
f=p/'gamma1-differential-regularity-route-643b.json';assert not f.exists();f.write_text(json.dumps(rd,indent=2)+'\n',encoding='utf-8')
s=(p/'record_gamma_one_differential_regularity_643.py').read_text(encoding='utf-8')
s=s.replace('-regularity-6-','-regularity-6b-').replace('DifferentialRegularityDependencyAudit6.log','DifferentialRegularityDependencyAudit6b.log').replace('route-643.json','route-643b.json')
ast.parse(s)
f=p/'record_gamma_one_differential_regularity_643b.py';assert not f.exists();f.write_text(s,encoding='utf-8')
print(json.dumps(dict(source=str(new),sha256=sha(new),mathematicalSourceChanges=False,exhaustiveAuditRerun=False)))
