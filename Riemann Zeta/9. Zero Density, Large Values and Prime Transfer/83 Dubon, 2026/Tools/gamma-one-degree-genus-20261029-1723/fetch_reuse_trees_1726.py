from pathlib import Path
from datetime import datetime,timezone
import urllib.request,json,hashlib,re
s=Path(__file__).parent;d=s/'targeted-reuse-refresh-20261029-1724';rows=[]
for repo in ['ImperialCollegeLondon/FLT','leanprover-community/mathlib4']:
 head=json.loads((d/(repo.replace('/','--')+'-head.json')).read_text(encoding='utf-8'))
 url='https://api.github.com/repos/'+repo+'/git/trees/'+head['commit']['tree']['sha']+'?recursive=1'
 req=urllib.request.Request(url,headers={'User-Agent':'Dubon-proof-reuse-review'})
 data=urllib.request.urlopen(req,timeout=25).read(8000001);assert len(data)<=8000000
 obj=json.loads(data);assert not obj.get('truncated')
 f=d/(repo.replace('/','--')+'-tree.json');assert not f.exists();f.write_bytes(data)
 paths=[x['path'] for x in obj['tree'] if x['type']=='blob' and x['path'].endswith('.lean')]
 chosen=[x for x in paths if re.search(r'ModularCurve|Genus|Automorph|SymmetricPower|ModularForm|GaloisRep',x,re.I)]
 rows.append(dict(repo=repo,pin=head['sha'],tree=head['commit']['tree']['sha'],url=url,path=str(f),sha256=hashlib.sha256(data).hexdigest().upper(),leanFiles=len(paths),candidatePaths=chosen))
 print(repo,'Lean files:',len(paths),'candidate paths:',len(chosen),flush=True)
f=d/'tree-review-inputs-1726.json';assert not f.exists();f.write_text(json.dumps(dict(recordedUTC=datetime.now(timezone.utc).isoformat(),repositories=rows),indent=2)+'\n',encoding='utf-8')
