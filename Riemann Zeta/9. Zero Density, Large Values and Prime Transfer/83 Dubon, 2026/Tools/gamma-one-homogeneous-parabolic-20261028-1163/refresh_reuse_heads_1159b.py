from pathlib import Path
from datetime import datetime,timezone
import json,urllib.request,hashlib,concurrent.futures
p=Path(__file__).parent
a=p/'reuse-head-refresh-1159b'
assert not a.exists()
a.mkdir()
prior=json.loads((p/'reuse-head-refresh-741/manifest.json').read_text())
repos={r['repository']:r['head'] for r in prior['repositories']}
repos['TauCetiProject/TauCeti']=None
repos['TauCetiProject/TauCetiRoadmap']=None
def fetch(item):
 repo,old=item
 url='https://api.github.com/repos/'+repo+'/commits?per_page=1'
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'Dubon-Lean-reuse-research','Accept':'application/vnd.github+json'})
  b=urllib.request.urlopen(req,timeout=30).read()
  f=a/(repo.replace('/','__')+'-head.json');f.write_bytes(b)
  v=json.loads(b)[0]
  return dict(repository=repo,previousHead=old,head=v['sha'],changed=old!=v['sha'],commitDate=v['commit']['committer']['date'],url=v['html_url'],retrievedUTC=datetime.now(timezone.utc).isoformat(),snapshot=str(f),sha256=hashlib.sha256(b).hexdigest().upper())
 except Exception as e:return dict(repository=repo,error=str(e),retrievedUTC=datetime.now(timezone.utc).isoformat())
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex:
 rows=list(ex.map(fetch,repos.items()))
with (a/'manifest.json').open('x',encoding='utf-8') as f:
 json.dump(dict(scope='October28 live default-branch refresh; source inspection only, no external proof closure audited or imported.',repositories=rows,rootPinsChanged=False,externalImport=False),f,indent=2);f.write('\n')
for r in rows:print(json.dumps(r),flush=True)

