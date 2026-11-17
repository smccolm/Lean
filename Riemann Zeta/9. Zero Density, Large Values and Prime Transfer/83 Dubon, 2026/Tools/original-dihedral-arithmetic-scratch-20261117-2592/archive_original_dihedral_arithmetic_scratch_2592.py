from pathlib import Path
import json,hashlib,re
s=Path(__file__).parent
p=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
c=json.loads((s/'source-original-dihedral-arithmetic-audit-config-2589.json').read_text())
r=json.loads((s/'source-original-dihedral-arithmetic-1-scratch-receipt.json').read_text())
assert r['exit']==r['diagnostics']==0
names={'source-original-dihedral-arithmetic-audit-config-2589.json','source-original-dihedral-arithmetic-1-scratch-receipt.json','source-original-dihedral-arithmetic-scratch-summary-2591.json','original-dihedral-arithmetic-reuse-review-2589.json','original-dihedral-character-route-review-2580.json','generate_original_dihedral_arithmetic_audits_2589.py','build_original_dihedral_arithmetic_2589.ps1','record_original_dihedral_arithmetic_scope_2591.py','archive_original_dihedral_arithmetic_scratch_2592.py','SourceOriginalDihedralArithmeticProductionSemantic2590.lean'}
for row in c['files']:
 f=Path(row['path']);assert sha(f)==row['canonicalSha256'];assert sha(Path(row['source']))==row['sourceSha256']
 names.update(f.stem+ext for ext in ['.lean','.log','.exit'])
 pat=re.compile(re.escape(f.stem)+r'\d{4}[a-z]?\.(lean|log|exit)$')
 names.update(x.name for x in s.iterdir() if x.is_file() and pat.fullmatch(x.name))
for stem in ['SourceOriginalDihedralArithmeticAudit1','SourceOriginalDihedralArithmeticDependencyAudit1','SourceOriginalDihedralArithmeticDeclarations2589','SourceOriginalDihedralArithmeticScratchSemantic2590']:
 names.update(stem+ext for ext in ['.lean','.log','.exit'])
 assert (s/(stem+'.exit')).read_text().strip()=='0'
 text=(s/(stem+'.log')).read_text('utf-16');assert not re.search(r'(warning:|error:|sorryAx|Found [1-9]|Try this:)',text)
assert all((s/name).is_file() for name in names)
dest=p/'Tools/original-dihedral-arithmetic-scratch-20261117-2592';assert not dest.exists()
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
manifest.write_text(json.dumps(dict(status='Scratch PASS: the same actual non-CM original integral/residual pair retains all earlier conclusions and constructs the literal nontrivial continuous quadratic character of every dihedral realization of its actual projective range. Negative values force original-field trace zero and original inertia is trivial away from Qp. The Dirichlet comparison and uniform conductor bound remain open. No final acceptance gate is closed. Production reconciliation and assembled verification remain pending.',modules=len(c['modules']),publicQueries=len(c['queries']),publicTheorems=len(c['theorems']),publicConstructions=len(c['constructions']),exhaustiveTheorems=r['exhaustiveTheorems'],otherDeclarations=r['exhaustiveOtherDeclarations'],lintersPerScope=16,requiredProofValueEdges=len(c['proofEdges']),typeValueFingerprints=r['semanticFingerprints']['declarations'],sourceObligations=['DUB-17 Theorem 2.6','DUB-18 Corollary 8.2'],priorEvidence='Tools/original-noncm-bounded-scratch-20261117-2571/manifest.json',accepted=16,total=20,failedAndUnexecutedDraftsRetained=True,files=rows),indent=2)+'\n')
cp=p/'Tools/scaffold.json';d=json.loads(cp.read_text(encoding='utf-8'));registered={x['path'] for x in d['files']}
for f in sorted(dest.iterdir()):
 if not f.is_file():continue
 rel=f.relative_to(p).as_posix();assert rel not in registered;d['files'].append(dict(path=rel,role='Tools'))
cp.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(json.dumps(dict(archived=len(rows),manifest=str(manifest),sha256=sha(manifest))))
