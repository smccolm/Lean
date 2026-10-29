from pathlib import Path
from datetime import datetime, timezone
import json, re, hashlib

p = Path(__file__).parent
cfg = json.loads((p / 'source-reduced-diamond-action-1-audit-config.json').read_text(encoding='utf-8'))
out = p / 'source-reduced-diamond-action-1-scratch-receipt.json'
review = p / 'source-reduced-diamond-action-1-reuse-review-20261029.json'
assert not out.exists() and not review.exists()
assert (len(cfg['modules']), len(cfg['queries']), len(cfg['proofEdges'])) == (20, 77, 98)
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
files = []
for m in cfg['modules']:
 f = p / (m + '.lean')
 code = re.sub(r'--[^\n]*', '', re.sub(r'/\-.*?\-/', '', f.read_text(encoding='utf-8'), flags=re.S))
 assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by)\b|set_option|nolint|trace_state', code), m
 ev = p / cfg['compileEvidence'][m]
 assert ev.with_suffix('.exit').read_text().strip() == '0' and ev.with_suffix('.log').stat().st_size == 0, m
 assert f.with_suffix('.olean').stat().st_mtime >= f.stat().st_mtime, m
 files.append(dict(path=str(f), sha256=sha(f), oleanSha256=sha(f.with_suffix('.olean')), compileLog=str(ev.with_suffix('.log')), compileExit=str(ev.with_suffix('.exit'))))
audit = p / 'SourceReducedDiamondActionAudit1.log'
dep = p / 'SourceReducedDiamondActionDependencyAudit1.log'
for f in [audit, dep]:
 assert f.with_suffix('.exit').read_text().strip() == '0'
 assert f.stat().st_mtime >= f.with_suffix('.lean').stat().st_mtime
text, dt = [f.read_text(encoding='utf-16') for f in [audit, dep]]
assert not re.search(r'warning:|error(?:\(|:)|PANIC|Try this:|sorryAx|Found [1-9]', text + dt)
assert text.count('All linting checks passed!') == text.count('with 16 linters') == 20
count = int(re.search(r'SOURCE REDUCED DIAMOND ACTION AUDIT PASS: (\d+) theorems', text)[1])
assert count >= len(cfg['theorems']) and 'all 98 required proof dependencies' in dt
found = re.findall(r"^'(.+)' depends on axioms:\s*\[([^]]*)\]", text, re.M)
free = re.findall(r"^'(.+)' does not depend on any axioms", text, re.M)
assert {n for n, _ in found} | set(free) == set(cfg['queries'])
for n, ax in found:
 assert set(x.strip() for x in ax.split(',') if x.strip()) <= {'propext', 'Classical.choice', 'Quot.sound'}, n
route = p / 'source-reduced-diamond-action-audit-route-1700.json'
rd = json.loads(route.read_text(encoding='utf-8'))
for row in rd['reuseChecked']:
 assert sha(Path(row['path'])) == row['sha256']
owner=p/'SourceReducedDiamondActionScratchOwnership1700.log'
assert owner.with_suffix('.exit').read_text().strip()=='0'
ot=owner.read_text(encoding='utf-16')
owned=re.findall(r'^OWNER ([^:]+): (.+)$',ot,re.M)
assert len(owned)==count and len(set(owned))==count and {m for m,n in owned}==set(cfg['modules'])
boundary = 'Scratch-audited only; promotion and assembled verification pending.'
rv = dict(date='2026-10-29 America/Vancouver', sourceDependency=rd['chain'],
 routeAssessment=dict(path=str(route), sha256=sha(route), review=rd),
 discharged=rd['assumptionsToDischarge'], remaining=rd['remaining'], boundary=boundary,
 rootPinsChanged=False, proofLimitsChanged=False)
review.write_text(json.dumps(rv, indent=2) + '\n', encoding='utf-8')
receipt = dict(separatelyAxiomChecked=cfg["separatelyAxiomChecked"], recordedUTC=datetime.now(timezone.utc).isoformat(),
 date=rv['date'], modules=cfg['modules'], files=files, queries=cfg['queries'],
 theoremRegistrations=cfg['theorems'], constructionRegistrations=cfg['constructions'],
 log=str(audit), logSha256=sha(audit), auditSha256=sha(audit.with_suffix('.lean')),
 exit=0, diagnostics=0, ownershipLog=str(owner), ownershipSha256=sha(owner), exhaustiveTheorems=count, linterScopes=20, lintersPerScope=16,
 requiredProofValueEdges=98, dependencyAuditLog=str(dep), dependencyAuditSha256=sha(dep),
 dependencyAuditSourceSha256=sha(dep.with_suffix('.lean')), consumers=cfg['roots'],
 dependency=rd['chain'], discharged=rd['assumptionsToDischarge'], boundary=boundary+' '+rd['remaining'],
 reuseReview=str(review), reuseReviewSha256=sha(review), rootPinsChanged=False, proofLimitsChanged=False)
out.write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
print(json.dumps(dict(receipt=str(out), sha256=sha(out), modules=20, queries=77,
 exhaustiveTheorems=count, proofEdges=98)))
