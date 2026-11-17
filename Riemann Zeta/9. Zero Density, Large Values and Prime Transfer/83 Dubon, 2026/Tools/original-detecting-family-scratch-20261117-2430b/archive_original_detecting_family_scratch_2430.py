from pathlib import Path
import json,hashlib,re

s=Path(__file__).parent
p=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
c=json.loads((s/'source-original-detecting-family-audit-config-2427.json').read_text())
r=json.loads((s/'source-original-detecting-family-2-scratch-receipt.json').read_text())
assert r['exit']==r['diagnostics']==0
sem=s/'SourceOriginalDetectingFamilyScratchSemantic2428.log'
assert sem.with_suffix('.exit').read_text().strip()=='0'
t=sem.read_text('utf-16');assert not re.search(r'(warning:|error:|sorryAx|Found [1-9]|Try this:)',t)
fingerprints=re.findall(r'^SEMANTIC (\S+) (\S+): (\d+) (\d+|NONE)$',t,re.M)
assert len(fingerprints)==len({n for _,n,_,_ in fingerprints})==r['exhaustiveTheorems']+r['exhaustiveOtherDeclarations']
names={'original-family-successor-review-2427.json','original-detecting-family-build-2427.log','original-detecting-family-build-2427.exit','prepare_original_detecting_family_audits_2418.py','source-original-detecting-family-audit-config-2418.json','original-detecting-family-reuse-review-2420.json','record_original_detecting_family_scope_2420.py','archive_original_detecting_family_scratch_2421.py','SourceOriginalDetectingFamilyAudit1.lean','SourceOriginalDetectingFamilyAudit1.log','SourceOriginalDetectingFamilyAudit1.exit','original-detecting-family-runner-review-2418.json','original-detecting-family-build-2418.log','original-detecting-family-build-2418.exit','original-detecting-family-build-2418b.log','original-detecting-family-build-2418b.exit','source-original-detecting-family-audit-config-2427.json','source-original-detecting-family-2-scratch-receipt.json',
 'source-original-detecting-family-scratch-summary-2429.json','original-detecting-family-reuse-review-2429.json',
 'prepare_original_detecting_family_audits_2427.py','build_original_detecting_families_2427.ps1',
 'record_original_detecting_family_scope_2429.py','SourceOriginalDetectingFamilyProductionSemantic2428.lean'}
for row in c['files']:
 f=Path(row['path']);assert sha(f)==row['canonicalSha256'];assert sha(Path(row['source']))==row['sourceSha256']
 names.update(f.stem+ext for ext in ['.lean','.log','.exit'])
 pattern=re.compile(re.escape(f.stem)+r'\d{4}[a-z]?\.(lean|log|exit)$')
 names.update(x.name for x in s.iterdir() if x.is_file() and pattern.fullmatch(x.name))
for name in ['SourceOriginalDetectingFamilyAudit2','SourceOriginalDetectingFamilyDependencyAudit2','SourceOriginalDetectingFamilyDeclarations2427','SourceOriginalDetectingFamilyScratchSemantic2428']:
 names.update(name+ext for ext in ['.lean','.log','.exit'])
dest=p/'Tools/original-detecting-family-scratch-20261117-2430';assert not dest.exists();dest.mkdir()
rows=[]
for name in sorted(names):
 f=s/name;assert f.is_file(),f
 target=dest/(name+('.txt' if f.suffix=='.lean' else ''));target.write_bytes(f.read_bytes())
 rows.append(dict(path=target.relative_to(p).as_posix(),sha256=sha(target)))
failed=s/'original-family-failed-audit-2418'
for f in sorted(failed.iterdir()):
 target=dest/('failed-2418-'+f.name);target.write_bytes(f.read_bytes())
 rows.append(dict(path=target.relative_to(p).as_posix(),sha256=sha(target)))
manifest=dest/'manifest.json'
manifest.write_text(json.dumps(dict(status='Scratch PASS: the same actual original residual representation has dimension-bounded jointly detecting regular-prime families for every original symmetric twisted H1 subspace on its finite linear subfield branch. Full arithmetic data and all preceding conclusions are retained. Production promotion and assembled verification remain pending.',
 modules=9,publicQueries=13,publicTheorems=8,publicConstructions=5,
 exhaustiveTheorems=r['exhaustiveTheorems'],otherDeclarations=r['exhaustiveOtherDeclarations'],
 lintersPerScope=16,requiredProofValueEdges=138,typeValueFingerprints=len(fingerprints),
 sourceObligations=['DUB-17 Theorem 2.6','DUB-18 Corollary 8.2'],
 priorEvidence='Tools/original-regular-prime-scratch-20261117-2408/manifest.json',
 accepted=16,total=20,failedAndUnexecutedDraftsRetained=True,files=rows),indent=2)+'\n')
cp=p/'Tools/scaffold.json';d=json.loads(cp.read_text(encoding='utf-8'));registered={x['path'] for x in d['files']}
for f in sorted(dest.iterdir()):
 rel=f.relative_to(p).as_posix();assert rel not in registered;d['files'].append(dict(path=rel,role='Tools'))
cp.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(json.dumps(dict(archived=len(rows),manifest=str(manifest),sha256=sha(manifest))))
