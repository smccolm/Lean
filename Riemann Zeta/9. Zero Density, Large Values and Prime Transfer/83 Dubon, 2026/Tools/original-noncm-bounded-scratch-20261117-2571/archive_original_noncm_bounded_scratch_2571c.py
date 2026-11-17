from pathlib import Path
import json,hashlib,re
s=Path(__file__).parent
p=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
c=json.loads((s/'source-original-noncm-bounded-audit-config-2568c.json').read_text())
r=json.loads((s/'source-original-noncm-bounded-1-scratch-receipt.json').read_text())
assert r['exit']==r['diagnostics']==0
names={'source-original-noncm-bounded-audit-config-2568.json','source-original-noncm-bounded-1-scratch-receipt.json','source-original-noncm-bounded-scratch-summary-2570.json','original-noncm-bounded-reuse-review-2568.json','generate_original_noncm_bounded_audits_2568.py','original-noncm-selftwist-route-review-2560.json','build_original_noncm_bounded_2568.ps1','record_original_noncm_bounded_scope_2570.py','archive_original_noncm_bounded_scratch_2571.py','SourceOriginalNonCMBoundedProductionSemantic2569b.lean'}
names.update(['source-original-noncm-bounded-audit-config-2568b.json', 'source-original-noncm-bounded-audit-config-2568c.json', 'record_original_noncm_bounded_scope_2570b.py', 'record_original_noncm_bounded_scope_2570c.py', 'record_original_noncm_bounded_scope_2570d.py', 'archive_original_noncm_bounded_scratch_2571b.py', 'archive_original_noncm_bounded_scratch_2571c.py', 'semantic-module-normalizer-repair-2572.json', 'SourceOriginalNonCMBoundedScratchSemantic2569.lean', 'SourceOriginalNonCMBoundedProductionSemantic2569.lean', 'SourceOriginalNonCMBoundedDependencyAudit1.lean', 'SourceOriginalNonCMBoundedDependencyAudit1.log', 'SourceOriginalNonCMBoundedDependencyAudit1.exit', 'SourceOriginalNonCMBoundedDependencyAudit2.lean', 'SourceOriginalNonCMBoundedDependencyAudit2.log', 'SourceOriginalNonCMBoundedDependencyAudit2.exit', 'SourceOriginalNonCMBoundedDependencyProbe2573.lean', 'SourceOriginalNonCMBoundedDependencyProbe2573.log', 'SourceOriginalNonCMBoundedDependencyProbe2573.exit'])
for row in c['files']:
 f=Path(row['path']);assert sha(f)==row['canonicalSha256'];assert sha(Path(row['source']))==row['sourceSha256']
 names.update(f.stem+ext for ext in ['.lean','.log','.exit'])
 pat=re.compile(re.escape(f.stem)+r'\d{4}[a-z]?\.(lean|log|exit)$')
 names.update(x.name for x in s.iterdir() if x.is_file() and pat.fullmatch(x.name))
for stem in ['SourceOriginalNonCMBoundedAudit1','SourceOriginalNonCMBoundedDependencyAudit3','SourceOriginalNonCMBoundedDeclarations2568','SourceOriginalNonCMBoundedScratchSemantic2569b']:
 names.update(stem+ext for ext in ['.lean','.log','.exit'])
 assert (s/(stem+'.exit')).read_text().strip()=='0'
 text=(s/(stem+'.log')).read_text('utf-16');assert not re.search(r'(warning:|error:|sorryAx|Found [1-9]|Try this:)',text)
assert all((s/name).is_file() for name in names)
dest=p/'Tools/original-noncm-bounded-scratch-20261117-2571';assert not dest.exists()
pending=[]
for name in sorted(names):
 f=s/name;target=dest/(name+('.txt' if f.suffix=='.lean' else ''))
 pending.append((target,f.read_bytes(),sha(f)))
assert len({target for target,_,_ in pending})==len(pending)
dest.mkdir();rows=[]
for target,data,digest in pending:
 target.write_bytes(data);assert sha(target)==digest
 rows.append(dict(path=target.relative_to(p).as_posix(),sha256=digest))
manifest=dest/'manifest.json'
manifest.write_text(json.dumps(dict(status='Scratch PASS: the same actual original non-CM integral/residual pair retains all prior conclusions and has a nonzero inert good-prime norm Frobenius trace for each source primitive nontrivial quadratic character of conductor at most M, above one form-dependent bound. The actual dihedral-character comparison and a conductor bound independent of characteristic remain open. No final acceptance gate is closed. Production reconciliation and assembled verification remain pending.',modules=len(c['modules']),publicQueries=len(c['queries']),publicTheorems=len(c['theorems']),publicConstructions=len(c['constructions']),exhaustiveTheorems=r['exhaustiveTheorems'],otherDeclarations=r['exhaustiveOtherDeclarations'],lintersPerScope=16,requiredProofValueEdges=len(c['proofEdges']),typeValueFingerprints=r['semanticFingerprints']['declarations'],sourceObligations=['DUB-17 Theorem 2.6','DUB-18 Corollary 8.2'],priorEvidence='Tools/original-exceptional-exclusion-scratch-20261117-2555/manifest.json',accepted=16,total=20,failedAndUnexecutedDraftsRetained=True,files=rows),indent=2)+'\n')
cp=p/'Tools/scaffold.json';d=json.loads(cp.read_text(encoding='utf-8'));registered={x['path'] for x in d['files']}
for f in sorted(dest.iterdir()):
 if not f.is_file():continue
 rel=f.relative_to(p).as_posix();assert rel not in registered;d['files'].append(dict(path=rel,role='Tools'))
cp.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(json.dumps(dict(archived=len(rows),manifest=str(manifest),sha256=sha(manifest))))
