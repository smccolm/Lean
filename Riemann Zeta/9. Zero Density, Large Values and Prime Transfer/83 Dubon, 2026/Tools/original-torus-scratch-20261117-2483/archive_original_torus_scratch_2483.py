from pathlib import Path
import json,hashlib,re
s=Path(__file__).parent
p=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
c=json.loads((s/'source-original-torus-audit-config-2480.json').read_text())
r=json.loads((s/'source-original-torus-2-scratch-receipt.json').read_text())
assert r['exit']==r['diagnostics']==0
sem=s/'SourceOriginalTorusScratchSemantic2481.log'
assert sem.with_suffix('.exit').read_text().strip()=='0'
t=sem.read_text('utf-16');assert not re.search(r'(warning:|error:|sorryAx|Found [1-9]|Try this:)',t)
fingerprints=re.findall(r'^SEMANTIC (\S+) (\S+): (\d+) (\d+|NONE)$',t,re.M)
assert len(fingerprints)==len({n for _,n,_,_ in fingerprints})==r['exhaustiveTheorems']+r['exhaustiveOtherDeclarations']
names={'source-original-torus-audit-config-2480.json','source-original-torus-2-scratch-receipt.json',
 'source-original-torus-scratch-summary-2482.json','original-torus-reuse-review-2471.json',
 'prepare_original_torus_audits_2469.py','prepare_original_torus_audits_2469b.py',
 'generate_original_torus_audits_2469.py','build_original_torus_2469.ps1',
 'record_original_torus_scope_2471.py','record_original_torus_scope_2471b.py',
 'original-torus-recorder-review-2471.json','original-torus-assembly-comment-review-2468.json',
 'build_original_torus_fresh_consumers_2468.ps1','SourceOriginalTorusProductionSemantic2481.lean',
 'original-local-dimension-route-review-2432.json','archive_original_torus_scratch_2472.py'}
for row in c['files']:
 f=Path(row['path']);assert sha(f)==row['canonicalSha256'];assert sha(Path(row['source']))==row['sourceSha256']
 names.update(f.stem+ext for ext in ['.lean','.log','.exit'])
 pattern=re.compile(re.escape(f.stem)+r'\d{4}[a-z]?\.(lean|log|exit)$')
 names.update(x.name for x in s.iterdir() if x.is_file() and pattern.fullmatch(x.name))
for stem in ['SourceOriginalSubfieldTraceDescent','SourceOriginalDistinctRootTraceDimension',
             'SourceOriginalSymmetricTorusDimension','SourceOriginalTorusFiniteFactorDimensions']:
 pattern=re.compile(re.escape(stem)+r'\d{4}[a-z]?\.(lean|log|exit)$')
 names.update(x.name for x in s.iterdir() if x.is_file() and pattern.fullmatch(x.name))
for stem in ['SourceOriginalTorusAudit2','SourceOriginalTorusDependencyAudit2','SourceOriginalTorusDeclarations2480','SourceOriginalTorusScratchSemantic2481']:
 names.update(stem+ext for ext in ['.lean','.log','.exit'])
names.update(['generate_original_torus_audits_2480.py','build_original_torus_2480.ps1',
 'record_original_torus_scope_2482.py','original-torus-reuse-review-2482.json',
 'original-torus-unused-parameter-review-2480.json','build_original_torus_parameter_revision_2480.ps1',
 'archive_original_torus_scratch_2483.py','source-original-torus-audit-config-2469.json',
 'SourceOriginalTorusAudit1.lean','SourceOriginalTorusAudit1.log','SourceOriginalTorusAudit1.exit'])
failed=s/'original-torus-failed-audit-2469'
failedManifest=json.loads((failed/'manifest.json').read_text())
for row in failedManifest['files']:assert sha(Path(row['path']))==row['sha256']
names.update(f.relative_to(s).as_posix() for f in failed.iterdir() if f.is_file())
for row in c['files']:
 for ext in ['.log','.exit']:
  f=s/(row['module']+'.pre2480'+ext)
  if f.exists():names.add(f.name)
# Validate the complete file set before creating or registering any archive.
assert all((s/name).is_file() for name in names)
dest=p/'Tools/original-torus-scratch-20261117-2483';assert not dest.exists()
pending=[]
for name in sorted(names):
 f=s/name;target=dest/(name+('.txt' if f.suffix=='.lean' else ''))
 pending.append((target,f.read_bytes(),sha(f)))
assert len({target for target,_,_ in pending})==len(pending)
dest.mkdir()
rows=[]
for target,data,digest in pending:
 target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data);assert sha(target)==digest
 rows.append(dict(path=target.relative_to(p).as_posix(),sha256=digest))
manifest=dest/'manifest.json'
manifest.write_text(json.dumps(dict(status='Scratch PASS: the same actual original modular-form residual representation has original split-torus detecting primes, exact unramified trace-zero adjoint H1 dimension equal to the symmetric degree, and bounded jointly detecting families with that dimension at every chosen prime. Every prior original conclusion and the explicit small-image alternative are retained. Production promotion and assembled verification remain pending.',
 modules=len(c['modules']),publicQueries=len(c['queries']),publicTheorems=len(c['theorems']),publicConstructions=len(c['constructions']),
 exhaustiveTheorems=r['exhaustiveTheorems'],otherDeclarations=r['exhaustiveOtherDeclarations'],
 lintersPerScope=16,requiredProofValueEdges=len(c['proofEdges']),typeValueFingerprints=len(fingerprints),
 sourceObligations=['DUB-17 Theorem 2.6','DUB-18 Corollary 8.2'],
 priorEvidence='Tools/original-unramified-dimension-scratch-20261117-2437/manifest.json',
 accepted=16,total=20,failedAndUnexecutedDraftsRetained=True,
 deferredRoutes=['Subfield trace descent and a separate invariant-kernel dimension argument are retained as unpromoted experiments; the selected prime-field torus and native cyclic-invariant route needs neither.'],files=rows),indent=2)+'\n')
cp=p/'Tools/scaffold.json';d=json.loads(cp.read_text(encoding='utf-8'));registered={x['path'] for x in d['files']}
for f in sorted(dest.rglob('*')):
 if not f.is_file():continue
 rel=f.relative_to(p).as_posix();assert rel not in registered;d['files'].append(dict(path=rel,role='Tools'))
cp.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(json.dumps(dict(archived=len(rows),manifest=str(manifest),sha256=sha(manifest))))
