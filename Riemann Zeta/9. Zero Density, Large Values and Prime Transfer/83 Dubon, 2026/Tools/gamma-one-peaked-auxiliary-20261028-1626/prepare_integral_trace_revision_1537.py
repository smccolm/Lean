from pathlib import Path
from datetime import datetime,timezone
import json,hashlib
s=Path(__file__).parent;out=s/'integral-trace-revision-1537';assert not out.exists()
assert (s/'SourceIntegralTraceAudit1.exit').read_text().strip()=='1'
log=(s/'SourceIntegralTraceAudit1.log').read_text(encoding='utf-16')
assert 'definition missing documentation string' in log and 'Translates.trSum' in log
assert log.count('linter reports:')==1
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
versions=json.loads((s/'integral-trace-versions-1531.json').read_text(encoding='utf-8'))
newversions=dict(versions);newversions['SourceIntegralTraceTranslates']='1517c'
pending=[];rows=[]
for m,v in versions.items():
 f=s/(m+v+'.lean');text=f.read_text(encoding='utf-8')
 newtext=text
 if m=='SourceIntegralTraceTranslates':
  needle='def trSum : ℍ → ℂ := '
  assert newtext.count(needle)==1
  newtext=newtext.replace(needle,'/-- The finite sum over the integer translations of one original cusp period. -/\n'+needle)
 # Only import routing changes in downstream versioned files.
 newtext=newtext.replace('import SourceIntegralTraceTranslates1517b\n','import SourceIntegralTraceTranslates1517c\n')
 vf=out/(m+newversions[m]+'.lean');pending.append((vf,newtext))
 canon=newtext
 for nm,nv in newversions.items():canon=canon.replace('import '+nm+nv+'\n','import '+nm+'\n')
 cf=out/(m+'.lean');pending.append((cf,canon))
 oldcanon=(s/(m+'.lean')).read_text(encoding='utf-8')
 expected=oldcanon
 if m=='SourceIntegralTraceTranslates':expected=expected.replace('def trSum : ℍ → ℂ := ','/-- The finite sum over the integer translations of one original cusp period. -/\ndef trSum : ℍ → ℂ := ')
 assert canon==expected,m
 rows.append(dict(module=m,originalCanonical=str(s/(m+'.lean')),originalSha256=sha(s/(m+'.lean')),newCanonical=str(cf),newSha256=hashlib.sha256(canon.encode()).hexdigest().upper(),proofBodyChanged=False,documentationAdded=(m=='SourceIntegralTraceTranslates')))
out.mkdir()
for f,t in pending:f.write_text(t,encoding='utf-8')
(out/'integral-trace-versions-1537.json').write_text(json.dumps(newversions,indent=2)+'\n',encoding='utf-8')
runner=(s/'build_integral_trace_canonical_1531.ps1').read_text(encoding='utf-8')
runner=runner.replace(str(s),str(out)).replace("$ev=$base+'-1531'","$ev=$base+'-1537'")
(out/'build_integral_trace_canonical_1537.ps1').write_text(runner,encoding='utf-8')
record=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),reason='The first frozen scratch audit failed exactly docBlame on the public trSum definition. Fresh independent source paths add its missing documentation string; all mathematical statements and proof bodies are unchanged. The original canonical sources, logs, scripts and failed audit remain immutable. No linter suppression or exclusion.',modules=rows,failedAudit=str(s/'SourceIntegralTraceAudit1.log'),failedAuditSha256=sha(s/'SourceIntegralTraceAudit1.log'),productionMutation=False,proofLimitsChanged=False)
(out/'revision-review-1537.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(path=str(out),modules=len(versions),proofBodiesChanged=0,documentationRepairs=1,originalEvidencePreserved=True)))
