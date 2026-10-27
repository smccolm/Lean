from pathlib import Path
import json,urllib.request,hashlib
p=Path(r"E:\Lean\.tmp\dubon83");a=p/"gamma-one-ramification-core-reuse-708"
t=json.loads((p/"reuse-head-refresh-630b/anthropics__fermats-last-theorem-tree.json").read_text(encoding="utf-8"));tree={r["path"]:r["sha"] for r in t["tree"]}
names=['P2M/Sol/S_ModularCurve_ComplexPlaceDictionaryOf_pt_eq_pt_iff_gammaH.lean', 'P2M/Sol/S_ModularCurve_ord_eq_three_of_ord_pos_and_ord_sub_eq_two_laurentBaseChange_gamma1.lean']
rows=[];commit="6e837e75355538c7f80bab5b956861e86c4eacc2"
for n in names:
 f=a/(Path(n).name+".txt");assert not f.exists()
 url="https://raw.githubusercontent.com/anthropics/fermats-last-theorem/"+commit+"/"+n
 b=urllib.request.urlopen(url,timeout=30).read();blob=hashlib.sha1(("blob "+str(len(b))+"\0").encode()+b).hexdigest();assert blob==tree[n]
 f.write_bytes(b);row=dict(path=n,file=str(f),url=url,bytes=len(b),gitBlob=blob,sha256=hashlib.sha256(b).hexdigest().upper());rows.append(row);print(json.dumps(row),flush=True)
with (a/"followup-snapshots.json").open("x",encoding="utf-8") as o:json.dump(dict(repository="anthropics/fermats-last-theorem",commit=commit,license="Apache-2.0",scope="Selected pinned source files only. No full closure, local build, import or pin change.",files=rows),o,indent=2);o.write("\n")
