from pathlib import Path
from datetime import datetime,timezone
import json,hashlib
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
src=p/'curve-reuse-1283b';dest=r/'Tools/curve-reuse-20261028-1283'
assert not dest.exists()
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
assert (p/'paper-verification-9026-console.exit').read_text().strip()=='0'
assert (r/'Tools/frobenius-diamond-20261028-1267/canonical-evidence-9026.json').is_file()
cp=r/'Tools/scaffold.json';c=json.loads(cp.read_text(encoding='utf-8'))
assert len(c['productionModules'])==9026
revisions=[]
for folder in sorted(src.iterdir()):
 if not folder.is_dir():continue
 meta=json.loads((folder/'fetch-manifest.json').read_text(encoding='utf-8'))
 revisions.append({k:meta[k] for k in ['repository','branch','revision','commitDate']})
 for f in folder.glob('*fetch-manifest*.json'):
  for row in json.loads(f.read_text(encoding='utf-8'))['files']:
   if row.get('status')==404:
    assert not (folder/row['path']).exists()
   else: assert sha(folder/row['path'])==row['sha256'],row['path']
files=[(f,dest/f.relative_to(src)) for f in sorted(src.rglob('*')) if f.is_file()]
for n in ['fetch_curve_reuse_1283.py','prepare_curve_reuse_fetch_1283b.py',
 'fetch_curve_reuse_1283b.py','fetch_curve_candidates_1283c.py',
 'fetch_curve_candidates_1283d.py','register_curve_reuse_1284.py']:
 files.append((p/n,dest/n))
report=p/'Dubon Curve Reuse Supplement 2026-10-28.md'
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
 status='AINTLIB contains substantive newer naive Gamma1 and scheme Weil-pairing bodies, but selected quotient geometry retains admissions and no original compact-curve specialization bridge was verified. ATLAS proves elliptic good-reduction torsion inertia with explicit good-reduction assumptions; it does not discharge the arbitrary-genus original Gamma1 input. Retain native fraction, coordinate and correspondence route; defer unrelated infrastructure. Bounded source review only. 16/20; DUB17--20 OPEN.')
out=dest/'review-manifest.json';out.write_text(json.dumps(review,indent=2)+'\n',encoding='utf-8')
c['files'].append(dict(path=out.relative_to(r).as_posix(),role='Tools'))
cp.write_text(json.dumps(c,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
for name in ['Dubon Sources.md','Tools/README.md']:
 f=r/name
 link=('' if name=='Dubon Sources.md' else '../')+'Dubon%20Curve%20Reuse%20Supplement%202026-10-28.md'
 f.write_text(f.read_text(encoding='utf-8')+'\n## Fresh curve and arithmetic candidates — 28 October 2026\n\nThe [curve reuse supplement]('+link+') inspects today\'s AINTLIB main and ATLAS revisions, with exact source hypotheses and remaining proof boundaries. The native original-field reduction route remains shorter for the required Dubon Frobenius/inertia chain. Pinned metadata and inert source evidence are retained in `Tools/curve-reuse-20261028-1283/`. No external build, import, full axiom audit or production adoption is claimed. DUB-17–20 remain open.\n',encoding='utf-8')
print(json.dumps(dict(registeredFiles=len(files)+1,manifest=str(out),sha256=sha(out),productionProofAdoption=False)))
