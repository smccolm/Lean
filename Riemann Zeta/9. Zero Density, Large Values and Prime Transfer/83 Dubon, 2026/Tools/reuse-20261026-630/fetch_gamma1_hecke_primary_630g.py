from pathlib import Path
import requests,json,hashlib,datetime,concurrent.futures
p=Path(r'E:\Lean\.tmp\dubon83\reuse-head-refresh-630e')
out=Path(r'E:\Lean\.tmp\dubon83\gamma1-hecke-primary-630g');assert not out.exists();out.mkdir()
repo='dozenalist/LeanModularForms'
commit=json.loads((p/'dozenalist__LeanModularForms-commit.json').read_text(encoding='utf-8'))['sha']
tree={x['path']:x for x in json.loads((p/'dozenalist__LeanModularForms-tree.json').read_text(encoding='utf-8'))['tree']}
paths=['LeanModularForms/HeckeRIngs/GL2/Gamma1Pair.lean','LeanModularForms/HeckeRIngs/GL2/HeckeT_p_Gamma1.lean','LeanModularForms/HeckeRIngs/GL2/CharacterDecomp.lean','LeanModularForms/HeckeRIngs/GL2/HeckeRingHomCharSpace.lean']
def fetch(path):
 url='https://raw.githubusercontent.com/'+repo+'/'+commit+'/'+path
 r=requests.get(url,timeout=45);r.raise_for_status();b=r.content
 git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert git==tree[path]['sha']
 f=out/(path+'.txt');f.parent.mkdir(parents=True,exist_ok=True);assert not f.exists();f.write_bytes(b)
 return dict(repo=repo,commit=commit,path=path,url=url,snapshot=str(f.relative_to(out)),gitBlob=git,sha256=hashlib.sha256(b).hexdigest().upper(),bytes=len(b))
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:rows=list(pool.map(fetch,paths))
(out/'snapshots.json').write_text(json.dumps(dict(retrievedUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),files=rows),indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(files=len(rows),bytes=sum(x['bytes'] for x in rows))))
