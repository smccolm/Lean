from pathlib import Path
import requests,json,hashlib,datetime,concurrent.futures
p=Path(r'E:\Lean\.tmp\dubon83\reuse-20261025-579')
out=Path(r'E:\Lean\.tmp\dubon83\gamma1-differential-input-reuse-633')
repo='anthropics/fermats-last-theorem'
commit=json.loads((p/'anthropics__fermats-last-theorem-commit.json').read_text(encoding='utf-8'))['sha']
tree={x['path']:x for x in json.loads((p/'anthropics__fermats-last-theorem-tree.json').read_text(encoding='utf-8'))['tree']}
paths=['P2M/Sol/S_CuspForm_exists_basis_gamma1_qCoeff_mem_range_ratCast.lean', 'P2M/Sol/S_ModularCurve_exists_coeffMap_diffQExp_x1FunctionFieldBar_eq_qExpansion.lean', 'P2M/Sol/S_ModularCurve_mem_regularDifferentials_x1FunctionFieldBar_of_coeffMap_diffQExp_eq_qExpansion.lean', 'P2M/Sol/S_ModularCurve_exists_cuspForm_coeffMap_diffQExp_x1FunctionFieldBar_eq_qExpansion_of_mem_regularDifferentials.lean']

def fetch(path):
 url='https://raw.githubusercontent.com/'+repo+'/'+commit+'/'+path
 r=requests.get(url,timeout=40);r.raise_for_status();b=r.content
 git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert git==tree[path]['sha']
 dest=out/(path+'.txt');dest.parent.mkdir(parents=True,exist_ok=True);assert not dest.exists();dest.write_bytes(b)
 return dict(repo=repo,commit=commit,path=path,url=url,snapshot=str(dest.relative_to(out)),gitBlob=git,sha256=hashlib.sha256(b).hexdigest().upper(),bytes=len(b))
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:rows=list(pool.map(fetch,paths))
f=out/'snapshots.json';assert not f.exists();f.write_text(json.dumps(dict(fetchedUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),files=rows),indent=2),encoding='utf-8')
print(json.dumps(dict(files=len(rows),bytes=sum(x['bytes'] for x in rows))))
