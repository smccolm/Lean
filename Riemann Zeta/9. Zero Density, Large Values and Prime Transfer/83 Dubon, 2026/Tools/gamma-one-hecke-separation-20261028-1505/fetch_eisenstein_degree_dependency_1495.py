from pathlib import Path
from datetime import datetime,timezone
from urllib.request import Request,urlopen
import json,hashlib
s=Path(__file__).parent
base=s/'anthropic-parabolic-tree-1462'
review=json.loads((base/'review-manifest.json').read_text(encoding='utf-8'))
tree=json.loads((base/'sol-tree.json').read_text(encoding='utf-8'));assert not tree.get('truncated',False)
names=['S_ModularCurve_exists_isIntegral_level_pow_mul_qExpansion_slash_coeff']
known={x['path'] for x in tree['tree']};assert all(n+'.lean' in known for n in names)
out=s/'anthropic-integral-slash-depth-1495';assert not out.exists();out.mkdir()
rows=[]
for n in names:
 path='P2M/Sol/'+n+'.lean';url='https://raw.githubusercontent.com/anthropics/fermats-last-theorem/'+review['revision']+'/'+path
 data=urlopen(Request(url,headers={'User-Agent':'Dubon-proof-reuse-review'}),timeout=45).read()
 f=out/(n+'.lean.txt')
 with f.open('xb') as h:h.write(data)
 rows.append(dict(path=path,local=str(f),url=url,sha256=hashlib.sha256(data).hexdigest().upper(),bytes=len(data)))
(out/'fetch-manifest.json').write_text(json.dumps(dict(recordedUTC=datetime.now(timezone.utc).isoformat(),repository=review['repository'],revision=review['revision'],files=rows,externalBuild=False,externalImport=False,productionMutation=False),indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(files=len(rows),bytes=sum(r['bytes'] for r in rows),revision=review['revision'])))
