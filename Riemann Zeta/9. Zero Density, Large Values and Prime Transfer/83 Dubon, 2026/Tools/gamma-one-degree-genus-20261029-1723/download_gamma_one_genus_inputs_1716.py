from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,urllib.request
s=Path(__file__).parent
dest=s/'anthropic-gamma-one-genus-inputs-1716'
assert not dest.exists()
pin='6e837e75355538c7f80bab5b956861e86c4eacc2'
names=['S_ModularCurve_two_mul_genusFF_add_card_fibres_le_finrank_add_two_of_gamma1_le.lean', 'S_ModularCurve_natCard_doubleCoset_le_card_fibres_of_finrank_eq_index.lean', 'S_ModularCurve_card_fibres_jqModC_qExpFunctionFieldC_gammaH_le_natCard_doubleCoset.lean', 'S_ModularCurve_two_mul_index_le_sum_ordDiff_D_add_natCard_doubleCoset_of_lt_five.lean']
tree=json.loads((s/'anthropic-parabolic-tree-1462/sol-tree.json').read_text(encoding='utf-8'))
entries={x['path']:x for x in tree['tree']}
downloaded=[]
for name in names:
 url='https://raw.githubusercontent.com/anthropics/fermats-last-theorem/'+pin+'/P2M/Sol/'+name
 data=urllib.request.urlopen(url,timeout=25).read(100001)
 entry=entries[name]
 assert len(data)==entry['size'] and len(data)<100000
 assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==entry['sha']
 downloaded.append((name,url,data))
dest.mkdir()
rows=[]
for name,url,data in downloaded:
 f=dest/(name+'.txt');f.write_bytes(data)
 rows.append(dict(path=str(f),url=url,bytes=len(data),sha256=hashlib.sha256(data).hexdigest().upper(),gitBlob=entries[name]['sha']))
manifest=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),pin=pin,files=rows,purpose='Read-only review of the exact remaining genus-preservation dependency after original Gamma1 degree preservation. Compare native original curves, fiber/cusp orbit classifications, canonical divisors and residue geometry against these four pinned source inputs; select only missing Gamma1 components. No external import, build, proof-option or source-contract change.',externalBuild=False,externalImport=False)
(dest/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')
print(json.dumps(manifest))
