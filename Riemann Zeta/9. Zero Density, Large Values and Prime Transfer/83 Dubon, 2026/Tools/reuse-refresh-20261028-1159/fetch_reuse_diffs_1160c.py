from pathlib import Path
import json,urllib.request,hashlib,concurrent.futures,difflib
p=Path(__file__).parent/'reuse-head-refresh-1159b'
rows={r['repository']:r for r in json.loads((p/'manifest.json').read_text())['repositories']}
jobs=[]
for repo in ['leanprover-community/mathlib4','teal-sea/zeta-lab']:
 delta=json.loads((p/(repo.replace('/','__')+'-complete-tree-delta.json')).read_text())['changed']
 paths=[x for x in delta if x.startswith('Mathlib/NumberTheory/ModularForms/') or x.startswith('Mathlib/NumberTheory/RamificationInertia/') or x.startswith('Mathlib/AlgebraicGeometry/') or (repo.endswith('zeta-lab') and x.endswith('.lean'))]
 for path in paths:
  for tag in ['head','previousHead']:
   name=repo.replace('/','__')+'__'+tag+'__'+path.replace('/','__')+'.txt'
   jobs.append((name,'https://raw.githubusercontent.com/'+repo+'/'+rows[repo][tag]+'/'+path))
def fetch(job):
 name,url=job;f=p/name;assert not f.exists()
 try:
  b=urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Dubon-Lean-reuse-research'}),timeout=30).read();f.write_bytes(b)
  return dict(path=str(f),url=url,sha256=hashlib.sha256(b).hexdigest().upper())
 except Exception as e:return dict(path=str(f),url=url,error=str(e))
with concurrent.futures.ThreadPoolExecutor(max_workers=6) as ex:out=list(ex.map(fetch,jobs))
for f in sorted(p.glob('*__head__*.txt')):
 old=p/f.name.replace('__head__','__previousHead__')
 if old.exists():
  dest=p/f.name.replace('__head__','__diff__');assert not dest.exists()
  dest.write_text(''.join(difflib.unified_diff(old.read_text(encoding='utf-8').splitlines(True),f.read_text(encoding='utf-8').splitlines(True),fromfile=old.name,tofile=f.name)),encoding='utf-8')
dest=p/'source-diffs-1160c.json';assert not dest.exists();dest.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(downloads=len(out),errors=[x for x in out if 'error' in x])))
