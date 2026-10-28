from pathlib import Path
from datetime import datetime,timezone
import json,urllib.request,hashlib,concurrent.futures
p=Path(__file__).parent/'reuse-head-refresh-1159b'
rows={r['repository']:r for r in json.loads((p/'manifest.json').read_text())['repositories']}
jobs=[]
for repo in ['leanprover-community/mathlib4','teal-sea/zeta-lab']:
 r=rows[repo]
 for tag in ['head','previousHead']:
  if repo.endswith('mathlib4') and tag=='previousHead':continue
  jobs.append((repo.replace('/','__')+'-'+tag+'-tree.json','https://api.github.com/repos/'+repo+'/git/trees/'+r[tag]+'?recursive=1'))
repo='TauCetiProject/TauCeti'; rev=rows[repo]['head']
tree=json.loads((p/'TauCetiProject__TauCeti-tree.json').read_text())['tree']
prefix='TauCeti/NumberTheory/ModularForms/'
selected=['ModularSymbols/Period/Integral.lean','ModularSymbols/Period/Map.lean','ModularSymbols/Period/Injective.lean','ModularSymbols/Period/Hecke.lean','ModularSymbols/Hecke/Diamond.lean','ModularSymbols/Hecke/Finite.lean','Newforms/Hecke/Integral.lean','Newforms/Hecke/Rational.lean','Newforms/Hecke/Stability.lean','Newforms/Hecke/Charpoly.lean','Newforms/NumberField.lean','Newforms/Satake.lean','Newforms/Fields.lean','Newforms/Basic.lean','Primitive.lean','GaloisProd.lean']
paths=[prefix+x for x in selected]+[x['path'] for x in tree if x['type']=='blob' and x['path'].startswith('TauCeti/AlgebraicGeometry/ModularCurve/')]
for path in paths:
 assert any(x['path']==path for x in tree),path
 jobs.append((repo.replace('/','__')+'__'+path.replace('/','__')+'.txt','https://raw.githubusercontent.com/'+repo+'/'+rev+'/'+path))
repo='TauCetiProject/TauCetiRoadmap';rev=rows[repo]['head']
for area in ['ModularForms','ModularCurves']:
 for name in ['README.md','STATUS.md','PROGRESS.md']:
  path='TauCetiRoadmap/'+area+'/'+name
  jobs.append((repo.replace('/','__')+'__'+path.replace('/','__')+'.txt','https://raw.githubusercontent.com/'+repo+'/'+rev+'/'+path))
def fetch(job):
 name,url=job;f=p/name;assert not f.exists()
 try:
  b=urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Dubon-Lean-reuse-research'}),timeout=45).read();f.write_bytes(b)
  return dict(path=str(f),url=url,sha256=hashlib.sha256(b).hexdigest().upper(),retrievedUTC=datetime.now(timezone.utc).isoformat())
 except Exception as e:return dict(url=url,error=str(e))
with concurrent.futures.ThreadPoolExecutor(max_workers=6) as ex:out=list(ex.map(fetch,jobs))
f=p/'source-fetch-1160b.json';assert not f.exists();f.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(downloads=len(out),errors=[x for x in out if 'error' in x])))
