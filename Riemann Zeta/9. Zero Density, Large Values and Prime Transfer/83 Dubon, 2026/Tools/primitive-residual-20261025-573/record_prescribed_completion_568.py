from pathlib import Path
from datetime import datetime,timezone
import json,re,hashlib
p=Path(__file__).parent
repo=Path(r'E:\Lean\Riemann Zeta')
prod=repo/'9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026/Extension/Dubon2026'
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
cfg=json.loads((p/'source-original-prescribed-completion-11-audit-config-568b.json').read_text())
out=p/'source-original-prescribed-completion-11-scratch-receipt.json'
rev=p/'source-original-prescribed-completion-11-reuse-review-20261025.json'
assert not out.exists() and not rev.exists()
assert (len(cfg['modules']),len(cfg['queries']),len(cfg['proofEdges']))==(11,21,31)
files=[]
for m in cfg['modules']:
 f=p/(m+'.lean');s=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',f.read_text(encoding='utf-8'),flags=re.S))
 assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by)\b|set_option|nolint|trace_state',s)
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 files.append(dict(path=str(f),sha256=sha(f),oleanSha256=sha(f.with_suffix('.olean'))))
audit=p/'SourceOriginalPrescribedCompletionAudit11b.log';dep=p/'SourceOriginalPrescribedCompletionDependencyAudit11b.log'
for f in [audit,dep]:
 assert f.with_suffix('.exit').read_text().strip()=='0'
 assert f.stat().st_mtime>=f.with_suffix('.lean').stat().st_mtime
text,dt=[f.read_text(encoding='utf-16') for f in [audit,dep]]
assert not re.search(r'warning:|error(?:\(|:)|PANIC|Try this:|sorryAx|Found [1-9]',text+dt)
assert text.count('All linting checks passed!')==text.count('with 16 linters')==11
count=int(re.search(r'SOURCE ORIGINAL PRESCRIBED COMPLETION AUDIT PASS: (\d+) theorems',text)[1])
assert count==77 and 'all 31 required proof dependencies' in dt
found=re.findall(r"^'(.+)' depends on axioms:\s*\[([^]]*)\]",text,re.M)
free=re.findall(r"^'(.+)' does not depend on any axioms",text,re.M)
assert {n for n,_ in found}|set(free)==set(cfg['queries'])
for n,ax in found:assert set(x.strip() for x in ax.split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'},n
route=p/'prescribed-completion-route-568b.json';rd=json.loads(route.read_text())
discharged=rd['assumptionsToDischarge']
remaining=rd['remaining']
boundary='Scratch-audited only; promotion and assembled verification pending.'
sources=[Path(row['path']) for row in rd['reuseChecked']]
for row in rd['reuseChecked']:assert sha(Path(row['path']))==row['sha256']

review=dict(date='2026-10-25 America/Vancouver',sourceDependency=rd['chain'],localReuse=[dict(path=str(f),sha256=sha(f)) for f in sources],routeAssessment=dict(path=str(route),sha256=sha(route),review=rd),discharged=discharged,remaining=remaining,boundary=boundary,rootPinsChanged=False,proofLimitsChanged=False)
repair=p/'prescribed-completion-documentation-successor-568b.json'
old=p/'SourceOriginalPrescribedCompletionAudit11'
assert old.with_suffix('.exit').read_text().strip()=='1'
lineage=dict(documentationRepair=str(repair),documentationRepairSha256=sha(repair),failedAuditSource=str(old.with_suffix('.lean')),failedAuditSourceSha256=sha(old.with_suffix('.lean')),failedAuditLog=str(old.with_suffix('.log')),failedAuditLogSha256=sha(old.with_suffix('.log')),reason='Four missing public definition docstrings repaired after preserving all 44 source/olean/compile snapshots and the original failed audit. The revised proofs and statements are textually unchanged after removing comments. Fresh audits pass; the used failed audit was not rerun.')
review['failedAuditLineage']=lineage
rev.write_text(json.dumps(review,indent=2)+'\n',encoding='utf-8')
receipt=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),date=review['date'],modules=cfg['modules'],files=files,queries=cfg['queries'],theoremRegistrations=cfg['theorems'],constructionRegistrations=cfg['constructions'],log=str(audit),logSha256=sha(audit),auditSha256=sha(audit.with_suffix('.lean')),exit=0,diagnostics=0,exhaustiveTheorems=count,linterScopes=11,lintersPerScope=16,requiredProofValueEdges=31,dependencyAuditLog=str(dep),dependencyAuditSha256=sha(dep),dependencyAuditSourceSha256=sha(dep.with_suffix('.lean')),consumers=cfg['roots'],dependency=rd['chain'],discharged=discharged,boundary=boundary+' '+remaining,reuseReview=str(rev),reuseReviewSha256=sha(rev),rootPinsChanged=False,proofLimitsChanged=False)
receipt['failedAuditLineage']=lineage
out.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(receipt=str(out),sha256=sha(out),modules=11,queries=21,exhaustiveTheorems=count,proofEdges=31)))
