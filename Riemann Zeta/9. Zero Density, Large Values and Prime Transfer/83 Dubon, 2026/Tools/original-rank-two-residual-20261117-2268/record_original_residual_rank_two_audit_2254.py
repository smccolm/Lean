from pathlib import Path
from datetime import datetime, timezone
import json, re, hashlib

p=Path(__file__).parent
cfg=json.loads((p/'original-residual-rank-two-audit-config-2253.json').read_text(encoding='utf-8'))
out=p/'source-original-residual-rank-two-1-scratch-receipt.json'
review=p/'source-original-residual-rank-two-1-reuse-review-20261117.json'
assert not out.exists() and not review.exists()
assert (len(cfg['modules']),len(cfg['queries']),len(cfg['proofEdges'])) == (7,15,33)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
files=[]
for m in cfg['modules']:
    f=p/(m+'.lean')
    code=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',f.read_text(encoding='utf-8'),flags=re.S))
    assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by)\b|set_option|nolint|trace_state',code),m
    tag='2253'
    ev=p/(m+'-'+tag)
    assert ev.with_suffix('.exit').read_text().strip()=='0' and ev.with_suffix('.log').stat().st_size==0,m
    assert f.with_suffix('.olean').stat().st_mtime >= f.stat().st_mtime,m
    files.append(dict(path=str(f),sha256=sha(f),oleanSha256=sha(f.with_suffix('.olean')),compileLog=str(ev.with_suffix('.log')),compileExit=str(ev.with_suffix('.exit'))))

audit=p/'SourceOriginalResidualRankTwoAudit1.log'
dep=p/'SourceOriginalResidualRankTwoDependencyAudit1.log'
owner=p/'SourceOriginalResidualRankTwoScratchOwnership2253.log'
for f in [audit,dep,owner]:
    assert f.with_suffix('.exit').read_text().strip()=='0',f
    assert f.stat().st_mtime >= f.with_suffix('.lean').stat().st_mtime
text,dt,ot=[f.read_text(encoding='utf-16') for f in [audit,dep,owner]]
assert not re.search(r'warning:|error(?:\(|:)|PANIC|Try this:|sorryAx|Found [1-9]',text+dt+ot)
assert text.count('All linting checks passed!') == text.count('with 16 linters') == 7
count=int(re.search(r'SOURCE ORIGINAL RESIDUAL RANK TWO AUDIT PASS: (\d+) theorems',text)[1])
assert count>=len(cfg['theorems']) and 'all 33 required proof dependencies' in dt
found=re.findall(r"^'(.+)' depends on axioms:\s*\[([^]]*)\]",text,re.M)
free=re.findall(r"^'(.+)' does not depend on any axioms",text,re.M)
assert {n for n,_ in found}|set(free)==set(cfg['queries'])
for n,ax in found:
    assert set(x.strip() for x in ax.split(',') if x.strip()) <= {'propext','Classical.choice','Quot.sound'},n
owned=re.findall(r'^OWNER ([^:]+): (.+)$',ot,re.M)
assert len(owned)==count and len(set(owned))==count and {m for m,n in owned}==set(cfg['modules'])
route=p/'original-residual-rank-two-route-2253.json'
rd=json.loads(route.read_text(encoding='utf-8'))
for row in rd['reuseChecked']:assert sha(Path(row['path']))==row['sha256']
boundary='Scratch-audited only; production promotion and assembled verification pending. '+rd['remaining']
rv=dict(date=rd['date'],sourceDependency=rd['chain'],routeAssessment=dict(path=str(route),sha256=sha(route),review=rd),
    discharged=rd['obligations'],remaining=rd['remaining'],boundary=boundary,rootPinsChanged=False,proofLimitsChanged=False)
review.write_text(json.dumps(rv,indent=2)+'\n',encoding='utf-8')
receipt=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),date=rv['date'],modules=cfg['modules'],files=files,
    queries=cfg['queries'],theoremRegistrations=cfg['theorems'],constructionRegistrations=cfg['constructions'],
    separatelyAxiomChecked=cfg['separatelyAxiomChecked'],log=str(audit),logSha256=sha(audit),auditSha256=sha(audit.with_suffix('.lean')),
    exit=0,diagnostics=0,ownershipLog=str(owner),ownershipSha256=sha(owner),exhaustiveTheorems=count,linterScopes=7,lintersPerScope=16,
    requiredProofValueEdges=33,dependencyAuditLog=str(dep),dependencyAuditSha256=sha(dep),dependencyAuditSourceSha256=sha(dep.with_suffix('.lean')),
    consumers=cfg['roots'],dependency=rd['chain'],discharged=rd['obligations'],boundary=boundary,
    reuseReview=str(review),reuseReviewSha256=sha(review),rootPinsChanged=False,proofLimitsChanged=False)
out.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(receipt=str(out),sha256=sha(out),modules=7,queries=15,exhaustiveTheorems=count,proofEdges=33)))
