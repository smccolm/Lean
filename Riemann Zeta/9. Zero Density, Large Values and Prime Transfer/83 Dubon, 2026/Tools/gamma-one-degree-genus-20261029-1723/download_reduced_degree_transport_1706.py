from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,urllib.request
s=Path(__file__).parent
dest=s/'anthropic-reduced-degree-transport-1706'
assert not dest.exists()
pin='6e837e75355538c7f80bab5b956861e86c4eacc2'
names=['S_ModularCurve_finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap.lean','S_ModularCurve_coeffMap_mem_qExpFunctionFieldC_and_eq_adjoin_image_coeffMap.lean']
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
manifest=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),pin=pin,files=rows,purpose='Read-only primary-source review of original reduced-field coefficient transport: transfer finite coordinate degree from the native residue image to the prime-field action and transfer the proved signed-index bound back. This discharges the remaining finite-degree input in the exact Gamma1 degree-preservation chain for DUB-17/18; no external import or proof-option change.',externalBuild=False,externalImport=False)
(dest/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')
print(json.dumps(manifest))
