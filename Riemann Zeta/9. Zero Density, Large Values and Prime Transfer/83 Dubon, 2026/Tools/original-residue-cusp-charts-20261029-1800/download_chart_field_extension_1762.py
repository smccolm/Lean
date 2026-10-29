from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,urllib.request
s=Path(__file__).parent
dest=s/'anthropic-chart-field-extension-1762'
assert not dest.exists()
pin='6e837e75355538c7f80bab5b956861e86c4eacc2'
names=['S_IntermediateField_exists_algHom_adjoin_apply_eq_of_isAlgebraic_of_transcendental.lean']
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
manifest=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),pin=pin,files=rows,purpose='Read-only pinned source review of the actual diamond-stabilizer charts over finite and cusp residue fibers. Native Galois place transitivity and fixed-field degree arguments are already available; inspect these exact remaining chart statements before expanding the reverse-genus dependency. No external import or proof options adopted.',externalBuild=False,externalImport=False)
(dest/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')
print(json.dumps(manifest))
