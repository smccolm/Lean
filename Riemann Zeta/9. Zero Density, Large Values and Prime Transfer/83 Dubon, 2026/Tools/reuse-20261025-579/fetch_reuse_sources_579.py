from pathlib import Path
import requests,json,hashlib,datetime,concurrent.futures
p=Path(r'E:\Lean\.tmp\dubon83\reuse-20261025-579')
rows=[]
for repo in ['lioristhmus/ramanujan-petersson','mkaratarakis/CICM24_Deligne','mkaratarakis/Deligne','tianyipeng/fermats-last-theorem']:
 stem=repo.replace('/','__')
 commit=json.loads((p/(stem+'-commit.json')).read_text())['sha']
 tree=json.loads((p/(stem+'-tree.json')).read_text())['tree']
 for e in tree:
  path=e['path']
  if e['type']!='blob':continue
  pick=(not repo.startswith('tianyipeng')) or path in ['README.md','lean-toolchain','lake-manifest.json','LICENSE','Definitions/Def_CuspForm_HeckeGaloisRepDatum.lean','Definitions/Def_GaloisRep_DeligneOrdinaryShape.lean'] or ('CuspForm_exists_galoisRep_of_point' in path) or ('PDivisibleGroup_exists_basis_padicComplex' in path)
  if pick and not path.endswith('.pdf'):rows.append((repo,commit,path))
def fetch(row):
 repo,commit,path=row
 url='https://raw.githubusercontent.com/'+repo+'/'+commit+'/'+path
 r=requests.get(url,timeout=40);r.raise_for_status()
 dest=p/(repo.replace('/','__'))/(path+'.txt')
 dest.parent.mkdir(parents=True,exist_ok=True)
 assert not dest.exists(),dest
 dest.write_bytes(r.content)
 return dict(repo=repo,commit=commit,path=path,url=url,snapshot=str(dest.relative_to(p)),sha256=hashlib.sha256(r.content).hexdigest().upper(),bytes=len(r.content))
with concurrent.futures.ThreadPoolExecutor(max_workers=5) as pool:
 result=list(pool.map(fetch,rows))
out=p/'primary-source-snapshots.json';assert not out.exists()
out.write_text(json.dumps(dict(fetchedUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),files=result),indent=2))
print(json.dumps({'downloaded':len(result),'bytes':sum(x['bytes'] for x in result),'manifest':str(out)}))
