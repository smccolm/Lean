from pathlib import Path
from datetime import datetime,timezone
import urllib.request,json,hashlib
s=Path(__file__).parent;dest=s/'targeted-reuse-refresh-20261029-1724'
assert not dest.exists()
repos=['anthropics/fermats-last-theorem','ImperialCollegeLondon/FLT','F-Najman/normalizer-lean','leanprover-community/mathlib4']
rows=[];payloads=[]
for repo in repos:
 url='https://api.github.com/repos/'+repo+'/commits/'+('master' if repo=='leanprover-community/mathlib4' else 'main')
 req=urllib.request.Request(url,headers={'User-Agent':'Dubon-proof-reuse-review','Accept':'application/vnd.github+json'})
 data=urllib.request.urlopen(req,timeout=25).read(2000001)
 assert len(data)<=2000000
 obj=json.loads(data);pin=obj['sha'];name=repo.replace('/','--')+'-head.json'
 payloads.append((name,data));rows.append(dict(repo=repo,url=url,pin=pin,date=obj['commit']['committer']['date'],sha256=hashlib.sha256(data).hexdigest().upper(),path=name))
 print(repo,pin,obj['commit']['committer']['date'],flush=True)
pin=next(x['pin'] for x in rows if x['repo']=='F-Najman/normalizer-lean')
for path in ['README.md','NormalizerDelta/Statements.lean','lean-toolchain']:
 url='https://raw.githubusercontent.com/F-Najman/normalizer-lean/'+pin+'/'+path
 data=urllib.request.urlopen(url,timeout=25).read(250001);assert len(data)<=250000
 name='normalizer-'+path.replace('/','--')+('.txt' if path.endswith('.lean') else '')
 payloads.append((name,data));rows.append(dict(repo='F-Najman/normalizer-lean',pin=pin,url=url,sha256=hashlib.sha256(data).hexdigest().upper(),path=name,bytes=len(data)))
dest.mkdir()
for name,data in payloads:(dest/name).write_bytes(data)
manifest=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),purpose='Fresh primary-source reuse check for DUB-17/18 original Gamma1 genus preservation and subsequent all-weight association/automorphy; inspected inert sources only, no external execution or import.',files=rows)
(dest/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf-8')
