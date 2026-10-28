from pathlib import Path
from datetime import datetime,timezone
import json,hashlib
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp=r/'Tools/scaffold.json';c=json.loads(cp.read_text(encoding='utf-8'))
dp=r/'Tools/lean-reuse-audit-20261015.json';d=json.loads(dp.read_text(encoding='utf-8'))
assert d['appliedSourceGammaOneArithmeticTateH1']['receipt8923']['exit']==0
assert (r/'Tools/gamma-one-arithmetic-tate-h1-20261027-1132/canonical-evidence-8923.json').exists()
assert len(c['productionModules'])==8923
key='liveLeanReuseRefresh20261028';assert key not in d
archive=r/'Tools/reuse-refresh-20261028-1159';assert not archive.exists()
report='Dubon Reuse Refresh 2026-10-28.md';assert not (r/report).exists()
pending=[]
for folder in ['reuse-head-refresh-1159','reuse-head-refresh-1159b']:
 for f in sorted((p/folder).rglob('*')):
  if f.is_file():pending.append((f,archive/folder/f.relative_to(p/folder)))
for name in ['refresh_reuse_heads_1159.py','refresh_reuse_heads_1159b.py','fetch_reuse_candidates_1160.py','fetch_reuse_sources_1160b.py','fetch_reuse_diffs_1160c.py','record_reuse_refresh_1164.py']:
 pending.append((p/name,archive/name))
heads=json.loads((p/'reuse-head-refresh-1159b/manifest.json').read_text())
assert len(heads['repositories'])==9 and all('head' in x for x in heads['repositories'])
registered={x['path'] for x in c['files']};files=[]
for src,dst in pending:
 assert src.exists() and not dst.exists();dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(src.read_bytes())
 rel=dst.relative_to(r).as_posix();assert rel not in registered
 c['files'].append(dict(path=rel,role='Tools'));registered.add(rel)
 files.append(dict(path=rel,sha256=sha(dst)))
(r/report).write_bytes((p/report).read_bytes());c['files'].append(dict(path=report,role='Research'))
record=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),scope='Nine fixed-revision repository heads; complete TauCeti tree inventories and complete old/new Mathlib and zeta-lab tree comparisons; selected proof-body inspection. No external import-closure compilation or axiom audit.',report=report,reportSha256=sha(r/report),heads=heads['repositories'],archive=archive.relative_to(r).as_posix(),files=files,rootPinsChanged=False,externalImportsAdded=False,fullGoal='16/20;DUB17--20 OPEN; all source obligations and acceptance gates unchanged')
dest=archive/'assessment.json';assert not dest.exists();dest.write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
c['files'].append(dict(path=dest.relative_to(r).as_posix(),role='Tools'))
for db in [dp,r/'Tools/lean-reuse-audit-20261020.json']:
 data=json.loads(db.read_text(encoding='utf-8'));assert key not in data
 data[key]=record;db.write_text(json.dumps(data,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
line='Fresh Lean reuse research (28 October 2026): nine fixed repository revisions and selected TauCeti diamond/period, integral Hecke and modular-curve proofs were assessed. The current [reuse report]({link}) records exact source contracts, coverage and remaining comparison obligations. No external closure is claimed locally audited or imported; root pins and DUB-17--20 remain unchanged.\n\n'
for name in ['Dubon Sources.md','Dubon Goal Prompt.md','Dependencies/README.md','Tools/README.md']:
 f=r/name;t=f.read_text(encoding='utf-8');pos=t.index('\n')+1
 link=('../' if '/' in name else '')+'Dubon%20Reuse%20Refresh%202026-10-28.md'
 f.write_text(t[:pos]+'\n'+line.format(link=link)+t[pos:].lstrip('\n'),encoding='utf-8')
cp.write_text(json.dumps(c,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(json.dumps(dict(report=str(r/report),files=len(files),assessment=str(dest),sha256=sha(dest))))
