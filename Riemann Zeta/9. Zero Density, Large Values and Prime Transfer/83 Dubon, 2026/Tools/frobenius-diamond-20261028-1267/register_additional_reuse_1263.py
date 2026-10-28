from pathlib import Path
from datetime import datetime, timezone
import json, hashlib
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
src=p/'followup-reuse-1251';dest=r/'Tools/additional-reuse-20261028-1251'
assert not dest.exists()
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
assert (p/'paper-verification-9007-console.exit').read_text().strip()=='0'
assert (r/'Tools/arithmetic-diamond-comparison-20261028-1241/canonical-evidence-9007.json').is_file()
cp=r/'Tools/scaffold.json';c=json.loads(cp.read_text(encoding='utf-8'))
assert len(c['productionModules'])==9007
revisions=[]
for folder in sorted(src.iterdir()):
 if not folder.is_dir():continue
 meta=json.loads((folder/'fetch-manifest.json').read_text(encoding='utf-8'))
 revisions.append({k:meta[k] for k in ['repository','revision','commitDate']})
 for f in folder.glob('*fetch-manifest*.json'):
  for row in json.loads(f.read_text(encoding='utf-8'))['files']:
   assert sha(folder/row['path'])==row['sha256'],row['path']
files=[(f,dest/f.relative_to(src)) for f in sorted(src.rglob('*')) if f.is_file()]
for n in ['fetch_followup_reuse_1251.py','fetch_followup_candidates_1251b.py',
 'fetch_followup_candidates_1251c.py','register_additional_reuse_1263.py']:
 files.append((p/n,dest/n))
report=p/'Dubon Additional Reuse Candidates 2026-10-28.md'
files.append((report,r/report.name))
rows=[]
for f,t in files:
 assert not t.exists(),t
 t.parent.mkdir(parents=True,exist_ok=True);t.write_bytes(f.read_bytes())
 rel=t.relative_to(r).as_posix()
 c['files'].append(dict(path=rel,role='root' if t.parent==r else 'Tools'))
 rows.append(dict(path=rel,sha256=sha(t),bytes=t.stat().st_size))
review=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),repositories=revisions,
 projectPinsChanged=False,files=rows,externalBuild=False,externalImport=False,
 externalAxiomAudit=False,productionProofAdoption=False,
 dependency='DUB17/18 -> literal higher symmetric continuation -> automorphy -> original all-weight association -> original Gamma1 geometric reduction, arithmetic Picard/Tate Frobenius and inertia comparison',
 status='Selected normalizer index formulas are a deferred candidate if the exact original genus/degree input requires them. Selected eml-lean statements have assumptions/admissions and do not supply the required construction. This is a bounded source review, not an assertion that no reusable proof exists. 16/20; DUB17--20 OPEN.')
out=dest/'review-manifest.json';out.write_text(json.dumps(review,indent=2)+'\n',encoding='utf-8')
c['files'].append(dict(path=out.relative_to(r).as_posix(),role='Tools'))
cp.write_text(json.dumps(c,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
for name in ['Dubon Sources.md','Tools/README.md']:
 f=r/name
 link=('' if name=='Dubon Sources.md' else '../')+'Dubon%20Additional%20Reuse%20Candidates%202026-10-28.md'
 f.write_text(f.read_text(encoding='utf-8')+'\n## Further pinned source review — 28 October 2026\n\nThe [additional candidate assessment]('+link+') records the exact normalizer-lean index formulas and the limitations of the selected eml-lean Eichler/Hecke declarations. It supplements the nine-repository refresh and NYLL review. Commit metadata, inert source text, fetch manifests and hashes are archived under `Tools/additional-reuse-20261028-1251/`. No external build, import, axiom audit or production proof adoption is claimed. DUB-17–20 remain open.\n',encoding='utf-8')
print(json.dumps(dict(registeredFiles=len(files)+1,manifest=str(out),sha256=sha(out),productionProofAdoption=False)))
