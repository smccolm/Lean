from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,ast
s=Path(__file__).parent;out=s/'integral-trace-revision-1537'
assert (out/'revision-review-1537.json').exists()
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
oldstem,newstem='source-integral-trace-1','source-integral-trace-2'
cfg=json.loads((s/(oldstem+'-audit-config.json')).read_text(encoding='utf-8'))
cfg['compileEvidence']={m:m+'-1537' for m in cfg['modules']}
def write(n,t):
 f=out/n;assert not f.exists(),f;f.write_text(t,encoding='utf-8')
write(newstem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
for a,b in [('SourceIntegralTraceAudit1','SourceIntegralTraceAudit2'),('SourceIntegralTraceDependencyAudit1','SourceIntegralTraceDependencyAudit2'),('SourceIntegralTraceScratchOwnership1532','SourceIntegralTraceScratchOwnership1538')]:
 write(b+'.lean',(s/(a+'.lean')).read_text(encoding='utf-8'))
route=json.loads((s/'source-integral-trace-audit-route-1532.json').read_text(encoding='utf-8'))
route['recordedUTC']=datetime.now(timezone.utc).isoformat()
route['revision']=dict(path=str(out/'revision-review-1537.json'),sha256=sha(out/'revision-review-1537.json'),reason='One missing translation-sum documentation string corrected in fresh canonical source paths. All original failed evidence preserved, mathematical statements and proof bodies unchanged, no suppression or exclusions.')
route['reuseChecked'].append(dict(path=str(out/'revision-review-1537.json'),sha256=sha(out/'revision-review-1537.json')))
write('source-integral-trace-audit-route-1538.json',json.dumps(route,indent=2)+'\n')
c=(s/'record_integral_trace_1532.py').read_text(encoding='utf-8')
for a,b in [(oldstem,newstem),('SourceIntegralTraceAudit1','SourceIntegralTraceAudit2'),('SourceIntegralTraceDependencyAudit1','SourceIntegralTraceDependencyAudit2'),('SourceIntegralTraceScratchOwnership1532','SourceIntegralTraceScratchOwnership1538'),('source-integral-trace-audit-route-1532','source-integral-trace-audit-route-1538')]:c=c.replace(a,b)
ast.parse(c);write('record_integral_trace_1538.py',c)
c=(s/'audit_integral_trace_1532.ps1').read_text(encoding='utf-8')
c=c.replace(str(s),str(out))
for a,b in [('SourceIntegralTraceAudit1','SourceIntegralTraceAudit2'),('SourceIntegralTraceDependencyAudit1','SourceIntegralTraceDependencyAudit2'),('SourceIntegralTraceScratchOwnership1532','SourceIntegralTraceScratchOwnership1538'),('record_integral_trace_1532','record_integral_trace_1538')]:c=c.replace(a,b)
write('audit_integral_trace_1538.ps1',c)
print(json.dumps(dict(modules=len(cfg['modules']),queries=len(cfg['queries']),proofEdges=len(cfg['proofEdges']),freshCheckpoint=str(out),originalFailedEvidencePreserved=True)))
