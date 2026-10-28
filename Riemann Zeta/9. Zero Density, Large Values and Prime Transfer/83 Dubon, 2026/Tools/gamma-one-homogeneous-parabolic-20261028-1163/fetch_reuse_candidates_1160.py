from pathlib import Path
from datetime import datetime,timezone
import json,urllib.request,hashlib,concurrent.futures
p=Path(__file__).parent/'reuse-head-refresh-1159b'
rows=json.loads((p/'manifest.json').read_text())['repositories']
jobs=[]
for r in rows:
 repo=r['repository'];base=repo.replace('/','__');rev=r['head']
 if r['changed'] and r['previousHead']:
  jobs.append((base+'-compare.json','https://api.github.com/repos/'+repo+'/compare/'+r['previousHead']+'...'+rev))
 if repo.startswith('TauCetiProject/'):
  jobs.append((base+'-tree.json','https://api.github.com/repos/'+repo+'/git/trees/'+rev+'?recursive=1'))
  for name in ['lean-toolchain','lake-manifest.json','LICENSE','README.md']:
   jobs.append((base+'-'+name+'.txt','https://raw.githubusercontent.com/'+repo+'/'+rev+'/'+name))
def fetch(job):
 name,url=job;f=p/name
 assert not f.exists()
 try:
  b=urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Dubon-Lean-reuse-research'}),timeout=45).read()
  f.write_bytes(b)
  return dict(path=str(f),url=url,sha256=hashlib.sha256(b).hexdigest().upper(),retrievedUTC=datetime.now(timezone.utc).isoformat())
 except Exception as e:return dict(url=url,error=str(e))
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex:out=list(ex.map(fetch,jobs))
f=p/'candidate-fetch-1160.json';assert not f.exists();f.write_text(json.dumps(out,indent=2)+'\n')
for x in out:print(json.dumps(x),flush=True)
