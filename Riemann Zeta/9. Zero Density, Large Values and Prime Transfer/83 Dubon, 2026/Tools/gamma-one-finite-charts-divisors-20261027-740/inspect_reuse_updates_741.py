from pathlib import Path
import json,urllib.request,hashlib
p=Path(r'E:\Lean\.tmp\dubon83');a=p/'reuse-head-refresh-741'
heads={r['repository']:r['head'] for r in json.loads((a/'manifest.json').read_text())['repositories']}
rows=[]
def fetch(url,f):
 assert not f.exists()
 req=urllib.request.Request(url,headers={'User-Agent':'Dubon-Lean-reuse-research','Accept':'application/vnd.github+json'})
 b=urllib.request.urlopen(req,timeout=60).read();f.write_bytes(b)
 return b
for repo in ['openai/math','leanprover-community/mathlib4']:
 url='https://api.github.com/repos/'+repo+'/git/trees/'+heads[repo]+'?recursive=1'
 f=a/(repo.replace('/','__')+'-tree.json');b=fetch(url,f);v=json.loads(b)
 row=dict(repository=repo,kind='recursive tree',url=url,path=str(f),sha256=hashlib.sha256(b).hexdigest().upper(),truncated=v.get('truncated'),entries=len(v['tree']))
 rows.append(row);print(json.dumps(row),flush=True)
for repo,names in {'openai/math':['CONTENTS.md','README.md','history.md'],
 'teal-sea/zeta-lab':['lean/ZetaLean/DavenportHeilbronn.lean','lean/ZetaLean/DHTrivialZero.lean','docs/47-the-davenport-heilbronn-zero.md']}.items():
 compare=json.loads((a/(repo.replace('/','__')+'-compare.json')).read_text(encoding='utf-8'))
 blobs={r['filename']:r['sha'] for r in compare['files']}
 for name in names:
  url='https://raw.githubusercontent.com/'+repo+'/'+heads[repo]+'/'+name
  f=a/(repo.replace('/','__')+'__'+Path(name).name+('.txt' if name.endswith('.lean') else ''))
  b=fetch(url,f);blob=hashlib.sha1(('blob '+str(len(b))+'\0').encode()+b).hexdigest();assert blob==blobs[name]
  row=dict(repository=repo,kind='selected primary file',source=name,url=url,path=str(f),sha256=hashlib.sha256(b).hexdigest().upper(),gitBlob=blob,bytes=len(b))
  rows.append(row);print(json.dumps(row),flush=True)
with (a/'selected-snapshots.json').open('x',encoding='utf-8') as f:json.dump(rows,f,indent=2);f.write('\n')
