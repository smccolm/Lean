from pathlib import Path
import json,hashlib,re
s=Path(__file__).parent
p=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
c=json.loads((s/'source-original-exceptional-exclusion-audit-config-2552.json').read_text())
r=json.loads((s/'source-original-exceptional-exclusion-1-scratch-receipt.json').read_text())
assert r['exit']==r['diagnostics']==0
names={'source-original-exceptional-exclusion-audit-config-2552.json','source-original-exceptional-exclusion-1-scratch-receipt.json','source-original-exceptional-exclusion-scratch-summary-2554.json','original-exceptional-exclusion-reuse-review-2552.json','generate_original_exceptional_exclusion_audits_2552.py','generate_original_exceptional_exclusion_audits_2552b.py','generate_original_exceptional_exclusion_audits_2552c.py','generate_original_exceptional_exclusion_audits_2552d.py','original-exceptional-image-route-review-2523.json','build_original_exceptional_exclusion_2552.ps1','record_original_exceptional_exclusion_scope_2554.py','archive_original_exceptional_exclusion_scratch_2555.py','archive_original_exceptional_exclusion_scratch_2555b.py','SourceOriginalExceptionalExclusionProductionSemantic2553b.lean'}
names.update(['archive_original_exceptional_exclusion_scratch_2555b.py', 'archive_original_exceptional_exclusion_scratch_2555c.py', 'record_original_exceptional_exclusion_scope_2554b.py', 'semantic-module-normalizer-repair-2572.json', 'SourceOriginalExceptionalExclusionScratchSemantic2553.lean', 'SourceOriginalExceptionalExclusionScratchSemantic2553.log', 'SourceOriginalExceptionalExclusionScratchSemantic2553.exit', 'SourceOriginalExceptionalExclusionProductionSemantic2553.lean'])
for row in c['files']:
 f=Path(row['path']);assert sha(f)==row['canonicalSha256'];assert sha(Path(row['source']))==row['sourceSha256']
 names.update(f.stem+ext for ext in ['.lean','.log','.exit'])
 pat=re.compile(re.escape(f.stem)+r'\d{4}[a-z]?\.(lean|log|exit)$')
 names.update(x.name for x in s.iterdir() if x.is_file() and pat.fullmatch(x.name))
for stem in ['SourceOriginalExceptionalExclusionAudit1','SourceOriginalExceptionalExclusionDependencyAudit1','SourceOriginalExceptionalExclusionDeclarations2552','SourceOriginalExceptionalExclusionScratchSemantic2553b']:
 names.update(stem+ext for ext in ['.lean','.log','.exit'])
 assert (s/(stem+'.exit')).read_text().strip()=='0'
 text=(s/(stem+'.log')).read_text('utf-16');assert not re.search(r'(warning:|error:|sorryAx|Found [1-9]|Try this:)',text)
assert all((s/name).is_file() for name in names)
dest=p/'Tools/original-exceptional-exclusion-scratch-20261117-2555';assert not dest.exists()
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
manifest.write_text(json.dumps(dict(status='Scratch PASS: a form-dependent bound removes the A4, S4 and A5 projective alternatives for the same original integral and residual representations. All prior arithmetic, Hecke, determinant, oddness, auxiliary-prime and CM deformation conclusions are retained. Exactly cyclic, dihedral and elementary-abelian-by-cyclic alternatives remain. Full source local conditions and higher continuation remain open. Production reconciliation and assembled verification remain pending.',modules=len(c['modules']),publicQueries=len(c['queries']),publicTheorems=len(c['theorems']),publicConstructions=len(c['constructions']),exhaustiveTheorems=r['exhaustiveTheorems'],otherDeclarations=r['exhaustiveOtherDeclarations'],lintersPerScope=16,requiredProofValueEdges=len(c['proofEdges']),typeValueFingerprints=r['semanticFingerprints']['declarations'],sourceObligations=['DUB-17 Theorem 2.6','DUB-18 Corollary 8.2'],priorEvidence='Tools/original-cm-inputs-20261117-2528/archive-manifest.json',accepted=16,total=20,failedAndUnexecutedDraftsRetained=True,files=rows),indent=2)+'\n')
cp=p/'Tools/scaffold.json';d=json.loads(cp.read_text(encoding='utf-8'));registered={x['path'] for x in d['files']}
for f in sorted(dest.iterdir()):
 if not f.is_file():continue
 rel=f.relative_to(p).as_posix();assert rel not in registered;d['files'].append(dict(path=rel,role='Tools'))
cp.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(json.dumps(dict(archived=len(rows),manifest=str(manifest),sha256=sha(manifest))))
