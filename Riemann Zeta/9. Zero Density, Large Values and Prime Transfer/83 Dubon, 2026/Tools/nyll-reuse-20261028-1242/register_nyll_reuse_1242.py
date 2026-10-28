from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,re
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
src=p/'nyll-reuse-1242b';dest=r/'Tools/nyll-reuse-20261028-1242'
assert not dest.exists()
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
manifests=['fetch-manifest.json','candidate-fetch-manifest-1242c.json','specialization-fetch-manifest-1242d.json']
for n in manifests:
 for row in json.loads((src/n).read_text())['files']:
  assert sha(src/row['path'])==row['sha256']
cp=r/'Tools/scaffold.json';c=json.loads(cp.read_text(encoding='utf-8'))
assert len(c['productionModules'])==9007
files=[]
for f in sorted(src.rglob('*')):
 if f.is_file():files.append((f,dest/f.relative_to(src)))
for f in (p/'nyll-reuse-1242').rglob('*'):
 if f.is_file():files.append((f,dest/'failed-sandbox-attempt'/f.name))
for n in ['fetch_nyll_reuse_1242.py','fetch_nyll_reuse_1242b.py','fetch_nyll_candidates_1242c.py','fetch_nyll_specialization_1242d.py','register_nyll_reuse_1242.py']:
 files.append((p/n,dest/n))
report=p/'Dubon NYLL Reuse Assessment 2026-10-28.md'
assert not (r/report.name).exists()
files.append((report,r/report.name))
rows=[]
for f,t in files:
 assert not t.exists(),t
 t.parent.mkdir(parents=True,exist_ok=True);t.write_bytes(f.read_bytes())
 rel=t.relative_to(r).as_posix()
 c['files'].append(dict(path=rel,role='root' if t.parent==r else 'Tools'))
 rows.append(dict(path=rel,sha256=sha(t),bytes=t.stat().st_size))
review=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),repository='n-yamaguchi-0729/NYLL',revision=json.loads((src/'fetch-manifest.json').read_text())['revision'],toolchain='leanprover/lean4:v4.35.0-rc2',projectPinsChanged=False,files=rows,externalBuild=False,externalImport=False,externalAxiomAudit=False,productionProofAdoption=False,dependency='DUB17/18 -> higher symmetric continuation -> automorphy -> original all-weight association -> original Gamma1 arithmetic Picard/Tate Frobenius and inertia comparison',status='Source candidate reviewed; exact original models and comparison hypotheses remain. 16/20; DUB17--20 OPEN.')
out=dest/'review-manifest.json';out.write_text(json.dumps(review,indent=2)+'\n',encoding='utf-8')
c['files'].append(dict(path=out.relative_to(r).as_posix(),role='Tools'))
cp.write_text(json.dumps(c,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
for name in ['Dubon Sources.md','Tools/README.md']:
 f=r/name
 link=('' if name=='Dubon Sources.md' else '../')+'Dubon%20NYLL%20Reuse%20Assessment%202026-10-28.md'
 f.write_text(f.read_text(encoding='utf-8')+'\n## Additional NYLL source review — 28 October 2026\n\nThe [pinned NYLL assessment]('+link+') records actual arithmetic Abel–Jacobi/Tate, Picard Frobenius and prime-to-residue torsion specialization candidates, their exact original-model assumptions, local overlap and the Lean-version gap. Sources and hashes are archived under `Tools/nyll-reuse-20261028-1242/`. No external build, import, axiom audit or production proof adoption is claimed. DUB-17–20 remain open.\n',encoding='utf-8')
print(json.dumps(dict(registeredFiles=len(files)+1,manifest=str(out),sha256=sha(out),productionProofAdoption=False)))
