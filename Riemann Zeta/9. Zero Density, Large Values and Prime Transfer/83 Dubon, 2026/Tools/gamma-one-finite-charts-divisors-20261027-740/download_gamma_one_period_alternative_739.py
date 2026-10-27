from pathlib import Path
import json, urllib.request, hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
a=p/'gamma-one-period-alternative-reuse-739'
assert not a.exists()
tree={r['path']:r['sha'] for r in json.loads((p/'reuse-head-refresh-630b/anthropics__fermats-last-theorem-tree.json').read_text(encoding='utf-8'))['tree']}
names=['P2M/Sol/S_ModularCurve_ComplexPlaceDictionaryOf_multiplier_eq_one_of_norm_eq_one_of_abelJacobi_mem_periodLatticeOf_gammaH.lean',
 'P2M/Sol/S_ModularCurve_exists_realizeOf_eventuallyEq_of_meromorphic_gammaH.lean',
 'P2M/Sol/S_ModularCurve_finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup.lean']
commit='6e837e75355538c7f80bab5b956861e86c4eacc2'
rows=[]
a.mkdir()
for n in names:
 url='https://raw.githubusercontent.com/anthropics/fermats-last-theorem/'+commit+'/'+n
 b=urllib.request.urlopen(url,timeout=30).read()
 blob=hashlib.sha1(('blob '+str(len(b))+'\0').encode()+b).hexdigest()
 assert blob==tree[n]
 f=a/(Path(n).name+'.txt');f.write_bytes(b)
 row=dict(path=n,file=str(f),url=url,bytes=len(b),gitBlob=blob,sha256=hashlib.sha256(b).hexdigest().upper())
 rows.append(row);print(json.dumps(row),flush=True)
with (a/'snapshots.json').open('x',encoding='utf-8') as f:
 json.dump(dict(repository='anthropics/fermats-last-theorem',commit=commit,license='Apache-2.0',
  scope='Assess the exact unresolved dimension/reciprocity/function-realization dependencies of the candidate principal-divisor route before adopting it. Selected primary source only; no full closure, local proof claim, import or pin change.',files=rows),f,indent=2);f.write('\n')
