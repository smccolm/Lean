from pathlib import Path
from datetime import datetime,timezone
import urllib.request,json,hashlib
s=Path(__file__).parent;d=s/'targeted-reuse-refresh-20261029-1724'
selected={'ImperialCollegeLondon/FLT':['FLT/GaloisRepresentation/Automorphic.lean','FLT/AutomorphicForm/QuaternionAlgebra/HeckeOperators/Concrete.lean'],'leanprover-community/mathlib4':['Mathlib/NumberTheory/ModularForms/LFunction.lean','Mathlib/NumberTheory/ModularForms/NormTrace.lean','Mathlib/NumberTheory/ModularForms/LevelOne/DimensionFormula.lean']}
rows=[]
for repo,paths in selected.items():
 head=json.loads((d/(repo.replace('/','--')+'-head.json')).read_text(encoding='utf-8'))
 tree=json.loads((d/(repo.replace('/','--')+'-tree.json')).read_text(encoding='utf-8'));entries={x['path']:x for x in tree['tree']}
 for path in paths:
  url='https://raw.githubusercontent.com/'+repo+'/'+head['sha']+'/'+path
  data=urllib.request.urlopen(url,timeout=25).read(250001);e=entries[path]
  assert len(data)==e['size'] and len(data)<=250000
  assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==e['sha']
  f=d/(repo.split('/')[0]+'--'+path.replace('/','--')+'.txt');assert not f.exists();f.write_bytes(data)
  rows.append(dict(repo=repo,pin=head['sha'],url=url,path=str(f),gitBlob=e['sha'],sha256=hashlib.sha256(data).hexdigest().upper(),bytes=len(data)))
  print(path,len(data),flush=True)
f=d/'selected-source-inputs-1728.json';assert not f.exists();f.write_text(json.dumps(dict(recordedUTC=datetime.now(timezone.utc).isoformat(),files=rows),indent=2)+'\n',encoding='utf-8')
