from pathlib import Path
from datetime import datetime, timezone
import hashlib,json
p=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
a=p/'Tools/gamma-one-finite-charts-divisors-20261027-740'
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
old=a/'archive-manifest-8586b.json'; new=a/'archive-manifest-8586d.json'; rec=a/'external-markdown-packaging-repair-8586d.json'
assert not new.exists() and not rec.exists()
m=json.loads(old.read_text(encoding='utf-8')); cp=p/'Tools/scaffold.json'; c=json.loads(cp.read_text(encoding='utf-8'))
sources=list(a.rglob('*.md')); assert len(sources)==4
changes={f.relative_to(p).as_posix():f.relative_to(p).as_posix()+'.txt' for f in sources}
for f in sources:
 assert not f.with_name(f.name+'.txt').exists()
 assert sum(x['path']==f.relative_to(p).as_posix() for x in m['files'])==1
for row in m['files']:assert sha(p/row['path'])==row['sha256']
record=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),reason='Four downloaded upstream Markdown snapshots also retain upstream-relative links. Store their identical bytes as plain-text research snapshots, while keeping all historical manifests immutable.',
 preflightFailure='INVENTORY FAIL: Broken local link in Tools/gamma-one-finite-charts-divisors-20261027-740/reuse-head-refresh-741/openai__math__CONTENTS.md: overview.pdf',preflightExit=1,
 predecessorManifest=dict(path=old.relative_to(p).as_posix(),sha256=sha(old)),relocations=[dict(oldPath=x,newPath=y,sha256=sha(p/x)) for x,y in changes.items()])
for f in sources:
 target=f.with_name(f.name+'.txt');target.write_bytes(f.read_bytes()); assert sha(f)==sha(target);f.unlink()
for collection in [m['files'],c['files']]:
 for row in collection:row['path']=changes.get(row['path'],row['path'])
new.write_text(json.dumps(m,indent=2)+'\n',encoding='utf-8');rec.write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
for f in [new,rec]:c['files'].append(dict(path=f.relative_to(p).as_posix(),role='Tools'))
cp.write_text(json.dumps(c,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
for name in ['lean-reuse-audit-20261015.json','lean-reuse-audit-20261020.json','source-gamma-one-finite-charts-divisors.json']:
 f=p/'Tools'/name;d=json.loads(f.read_text(encoding='utf-8'));k=d.get('appliedSourceGammaOneFiniteChartsDivisors',d)
 k['externalMarkdownPackagingRepair8586d']=dict(path=rec.relative_to(p).as_posix(),sha256=sha(rec))
 if 'proofEvidenceArchive' in k:k['proofEvidenceArchive'].update(manifest=new.relative_to(p).as_posix(),sha256=sha(new))
 f.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
print(json.dumps(record))
