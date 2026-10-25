from pathlib import Path
from datetime import datetime,timezone
import json,re,hashlib
p=Path(__file__).parent
repo=Path(r'E:\Lean\Riemann Zeta')
prod=repo/'9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026/Extension/Dubon2026'
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
cfg=json.loads((p/'source-original-primitive-rank-two-17-audit-config-562b.json').read_text())
out=p/'source-original-primitive-rank-two-17-scratch-receipt.json'
rev=p/'source-original-primitive-rank-two-17-reuse-review-20261025.json'
assert not out.exists() and not rev.exists()
assert (len(cfg['modules']),len(cfg['queries']),len(cfg['proofEdges']))==(17,35,45)
files=[]
for m in cfg['modules']:
 f=p/(m+'.lean');s=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',f.read_text(encoding='utf-8'),flags=re.S))
 assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by)\b|set_option|nolint|trace_state',s)
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 files.append(dict(path=str(f),sha256=sha(f),oleanSha256=sha(f.with_suffix('.olean'))))
audit=p/'SourceOriginalPrimitiveRankTwoAudit17.log';dep=p/'SourceOriginalPrimitiveRankTwoDependencyAudit17b.log'
for f in [audit,dep]:
 assert f.with_suffix('.exit').read_text().strip()=='0'
 assert f.stat().st_mtime>=f.with_suffix('.lean').stat().st_mtime
text,dt=[f.read_text(encoding='utf-16') for f in [audit,dep]]
assert not re.search(r'warning:|error(?:\(|:)|PANIC|Try this:|sorryAx|Found [1-9]',text+dt)
assert text.count('All linting checks passed!')==text.count('with 16 linters')==17
count=int(re.search(r'SOURCE ORIGINAL PRIMITIVE RANK TWO AUDIT PASS: (\d+) theorems',text)[1])
assert count==80 and 'all 45 required proof dependencies' in dt
found=re.findall(r"^'(.+)' depends on axioms:\s*\[([^]]*)\]",text,re.M)
free=re.findall(r"^'(.+)' does not depend on any axioms",text,re.M)
assert {n for n,_ in found}|set(free)==set(cfg['queries'])
for n,ax in found:assert set(x.strip() for x in ax.split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'},n
route=p/'primitive-rank-two-route-562b.json';rd=json.loads(route.read_text())
discharged='The literal arithmetic primitive projector now has a nonzero rank-two image on the actual coefficient-extended original Tate module. Its same image has an injective restriction of the original root-valued Weil pairing. The original integral cusp Hecke presentation, all-word rank-two Tate coordinates, native finite-product scalar extension, prescribed p-adic eigencharacter and character-normalized idempotent ideal supply the coordinate equivalence. Generator, character-compatibility, image-dimension and nondegeneracy premises are derived for the actual consumer. Comparison to the existing spanning primitive specialization and the separate Frobenius determinant remain required.'
remaining=rd['remaining']
boundary='Scratch-audited only; promotion and assembled verification pending.'
sources=[Path(row['path']) for row in rd['reuseChecked']]
for row in rd['reuseChecked']:assert sha(Path(row['path']))==row['sha256']
prior=p/'source-original-primitive-tate-restriction-8-scratch-receipt.json'
assert sha(prior)=='A2685A2906062D51BA45D445940FA864D0BABC19FCFD726372D899D7BBB526F6'

review=dict(date='2026-10-25 America/Vancouver',sourceDependency=rd['chain'],localReuse=[dict(path=str(f),sha256=sha(f)) for f in sources],routeAssessment=dict(path=str(route),sha256=sha(route),review=rd),discharged=discharged,remaining=remaining,boundary=boundary,precedingScratchReceipt=dict(path=str(prior),sha256=sha(prior)),rootPinsChanged=False,proofLimitsChanged=False)
rev.write_text(json.dumps(review,indent=2)+'\n',encoding='utf-8')
receipt=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),date=review['date'],modules=cfg['modules'],files=files,queries=cfg['queries'],theoremRegistrations=cfg['theorems'],constructionRegistrations=cfg['constructions'],log=str(audit),logSha256=sha(audit),auditSha256=sha(audit.with_suffix('.lean')),exit=0,diagnostics=0,exhaustiveTheorems=count,linterScopes=17,lintersPerScope=16,requiredProofValueEdges=45,dependencyAuditLog=str(dep),dependencyAuditSha256=sha(dep),dependencyAuditSourceSha256=sha(dep.with_suffix('.lean')),consumers=cfg['roots'],dependency=rd['chain'],discharged=discharged,boundary=boundary+' '+remaining,reuseReview=str(rev),reuseReviewSha256=sha(rev),rootPinsChanged=False,proofLimitsChanged=False)
receipt['dependencyAuditLineage']=rd['dependencyAuditLineage']
receipt['separatelyAxiomCheckedDefinitionalLaws']=cfg['separatelyAxiomCheckedDefinitionalLaws']
out.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(receipt=str(out),sha256=sha(out),modules=17,queries=35,exhaustiveTheorems=count,proofEdges=45)))
