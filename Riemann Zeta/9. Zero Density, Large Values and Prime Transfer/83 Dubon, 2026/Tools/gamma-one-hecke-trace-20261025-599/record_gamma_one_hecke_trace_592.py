from pathlib import Path
from datetime import datetime,timezone
import json,re,hashlib
p=Path(__file__).parent
repo=Path(r'E:\Lean\Riemann Zeta')
prod=repo/'9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026/Extension/Dubon2026'
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
cfg=json.loads((p/'source-gamma-one-hecke-trace-7-audit-config.json').read_text())
out=p/'source-gamma-one-hecke-trace-7-scratch-receipt.json'
rev=p/'source-gamma-one-hecke-trace-7-reuse-review-20261025.json'
assert not out.exists() and not rev.exists()
assert (len(cfg['modules']),len(cfg['queries']),len(cfg['proofEdges']))==(7,24,36)
files=[]
for m in cfg['modules']:
 f=p/(m+'.lean');s=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',f.read_text(encoding='utf-8'),flags=re.S))
 assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by)\b|set_option|nolint|trace_state',s)
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 files.append(dict(path=str(f),sha256=sha(f),oleanSha256=sha(f.with_suffix('.olean'))))
audit=p/'SourceGammaOneHeckeTraceAudit7.log';dep=p/'SourceGammaOneHeckeTraceDependencyAudit7.log'
for f in [audit,dep]:
 assert f.with_suffix('.exit').read_text().strip()=='0'
 assert f.stat().st_mtime>=f.with_suffix('.lean').stat().st_mtime
text,dt=[f.read_text(encoding='utf-16') for f in [audit,dep]]
assert not re.search(r'warning:|error(?:\(|:)|PANIC|Try this:|sorryAx|Found [1-9]',text+dt)
assert text.count('All linting checks passed!')==text.count('with 16 linters')==7
count=int(re.search(r'SOURCE GAMMA ONE HECKE TRACE AUDIT PASS: (\d+) theorems',text)[1])
assert count>=len(cfg['theorems']) and 'all 36 required proof dependencies' in dt
found=re.findall(r"^'(.+)' depends on axioms:\s*\[([^]]*)\]",text,re.M)
free=re.findall(r"^'(.+)' does not depend on any axioms",text,re.M)
assert {n for n,_ in found}|set(free)==set(cfg['queries'])
for n,ax in found:assert set(x.strip() for x in ax.split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'},n
route=p/'gamma1-hecke-comparison-route-592.json';rd=json.loads(route.read_text())
discharged=rd['assumptionsToDischarge']
remaining=rd['remaining']
boundary='Scratch-audited only; promotion and assembled verification pending.'
sources=[Path(row['path']) for row in rd['reuseChecked']]
for row in rd['reuseChecked']:assert sha(Path(row['path']))==row['sha256']

primaryManifest=p/rd['primaryReview']
primary=json.loads(primaryManifest.read_text(encoding='utf-8'))
for row in primary['files']:
 f=primaryManifest.parent/row['snapshot']
 assert sha(f)==row['sha256']
 b=f.read_bytes()
 assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==row['gitBlob']
review=dict(date='2026-10-25 America/Vancouver',sourceDependency=rd['chain'],localReuse=[dict(path=str(f),sha256=sha(f)) for f in sources],routeAssessment=dict(path=str(route),sha256=sha(route),review=rd),discharged=discharged,remaining=remaining,boundary=boundary,rootPinsChanged=False,proofLimitsChanged=False)
review['primaryGammaOneReview']=dict(manifest=str(primaryManifest),sha256=sha(primaryManifest),files=primary['files'],finding='The inspected Gamma1 arithmetic construction takes a characteristic-zero rational Hecke-and-diamond character. It does not itself realize the original finite permutation characters. The genuine Gamma1 correspondence and the exact native/literal H1 transfer identity now supply the required convention links. The actual literal transfer is proved surjective; its Hecke-and-diamond compatibility and geometric arithmetic realization remain open.',externalImport=False)
rev.write_text(json.dumps(review,indent=2)+'\n',encoding='utf-8')
receipt=dict(separatelyAxiomChecked=cfg['separatelyAxiomChecked'],recordedUTC=datetime.now(timezone.utc).isoformat(),date=review['date'],modules=cfg['modules'],files=files,queries=cfg['queries'],theoremRegistrations=cfg['theorems'],constructionRegistrations=cfg['constructions'],log=str(audit),logSha256=sha(audit),auditSha256=sha(audit.with_suffix('.lean')),exit=0,diagnostics=0,exhaustiveTheorems=count,linterScopes=7,lintersPerScope=16,requiredProofValueEdges=36,dependencyAuditLog=str(dep),dependencyAuditSha256=sha(dep),dependencyAuditSourceSha256=sha(dep.with_suffix('.lean')),consumers=cfg['roots'],dependency=rd['chain'],discharged=discharged,boundary=boundary+' '+remaining,reuseReview=str(rev),reuseReviewSha256=sha(rev),rootPinsChanged=False,proofLimitsChanged=False)
out.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(receipt=str(out),sha256=sha(out),modules=7,queries=24,exhaustiveTheorems=count,proofEdges=36)))
