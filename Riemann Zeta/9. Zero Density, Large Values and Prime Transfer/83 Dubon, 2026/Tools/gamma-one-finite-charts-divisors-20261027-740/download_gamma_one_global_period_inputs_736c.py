from pathlib import Path
import json,urllib.request,hashlib
p=Path(r'E:\Lean\.tmp\dubon83');a=p/'gamma-one-global-period-route-reuse-736'
assert a.is_dir()
t=json.loads((p/'reuse-head-refresh-630b/anthropics__fermats-last-theorem-tree.json').read_text(encoding='utf-8'))
tree={r['path']:r['sha'] for r in t['tree']}
names=['Definitions/Def_ModularCurve_ComplexPlaceDictionaryOf.lean','P2M/Sol/S_ModularCurve_ord_eq_zero_of_not_mem_of_realizeOf_tendsto.lean','P2M/Sol/S_ModularCurve_ComplexPlaceDictionaryOf_exists_cuspForm_mul_exp_periodOf_eq_one_of_abelJacobi_mem_periodLatticeOf_gammaH.lean']
rows=[];commit='6e837e75355538c7f80bab5b956861e86c4eacc2'
for n in names:
 f=a/(Path(n).name+'.txt');assert not f.exists()
 url='https://raw.githubusercontent.com/anthropics/fermats-last-theorem/'+commit+'/'+n
 b=urllib.request.urlopen(url,timeout=30).read()
 blob=hashlib.sha1(('blob '+str(len(b))+'\0').encode()+b).hexdigest();assert blob==tree[n]
 f.write_bytes(b);row=dict(path=n,file=str(f),url=url,bytes=len(b),gitBlob=blob,sha256=hashlib.sha256(b).hexdigest().upper())
 rows.append(row);print(json.dumps(row),flush=True)
with (a/'followup-snapshots.json').open('x',encoding='utf-8') as f:
 json.dump(dict(repository='anthropics/fermats-last-theorem',commit=commit,license='Apache-2.0',scope='Selected pinned source files only. Assess whether the exact actual Gamma1 period/Picard contract has a shorter rigorous route before expanding cusp/global chart infrastructure. No full closure, local build, import or pin change.',files=rows),f,indent=2);f.write('\n')
