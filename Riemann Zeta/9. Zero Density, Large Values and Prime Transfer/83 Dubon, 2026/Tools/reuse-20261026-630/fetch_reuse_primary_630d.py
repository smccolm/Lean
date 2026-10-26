from pathlib import Path
import requests,json,hashlib,datetime,concurrent.futures
p=Path(r'E:\Lean\.tmp\dubon83')
root=p/'reuse-primary-followup-630c'
out=p/'reuse-primary-followup-630d';assert not out.exists();out.mkdir()
meta=json.loads((root/'openai-number-theory-tree.json').read_text())
repo='openai/math';commit=meta['commit']
tree={x['path']:x for x in meta['result']['tree']}
paths=['CubicMoment/Theta/CubicThetaRamanujan.lean','CubicMoment/Theta/CubicThetaPrimeCubeRootRamanujan.lean','DirichletL/Hecke/Nonvanishing.lean']
def fetch(path):
 full='lean/OAI/NumberTheory/'+path
 url='https://raw.githubusercontent.com/'+repo+'/'+commit+'/'+full
 r=requests.get(url,timeout=45);r.raise_for_status();b=r.content
 git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert git==tree[path]['sha']
 f=out/(full+'.txt');f.parent.mkdir(parents=True,exist_ok=True);assert not f.exists();f.write_bytes(b)
 return dict(repo=repo,commit=commit,path=full,url=url,snapshot=str(f.relative_to(out)),gitBlob=git,sha256=hashlib.sha256(b).hexdigest().upper(),bytes=len(b))
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:rows=list(pool.map(fetch,paths))
(out/'snapshots.json').write_text(json.dumps(dict(retrievedUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),files=rows),indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(files=len(rows),bytes=sum(x['bytes'] for x in rows))))
