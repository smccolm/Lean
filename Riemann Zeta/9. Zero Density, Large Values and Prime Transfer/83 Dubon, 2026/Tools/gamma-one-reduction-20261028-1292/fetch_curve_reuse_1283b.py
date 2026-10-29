from pathlib import Path
from datetime import datetime,timezone
from urllib.request import Request,urlopen
from urllib.error import HTTPError
from concurrent.futures import ThreadPoolExecutor
import json,hashlib
p=Path(__file__).parent/'curve-reuse-1283b'
p.mkdir(exist_ok=False)
def review(target):
 repo,branch=target
 root=p/(repo.replace('/','--')+'--'+branch.replace('/','--'));root.mkdir()
 records=[]
 def fetch(url,name,optional=False):
  try:
   data=urlopen(Request(url,headers={'User-Agent':'Dubon-proof-reuse-review','Accept':'application/vnd.github+json'}),timeout=40).read()
  except HTTPError as e:
   if optional and e.code==404:
    records.append(dict(url=url,path=name,status=404));return None
   raise
  f=root/name;f.parent.mkdir(parents=True,exist_ok=True);assert not f.exists();f.write_bytes(data)
  records.append(dict(url=url,path=name,sha256=hashlib.sha256(data).hexdigest().upper(),bytes=len(data)))
  return data
 base='https://api.github.com/repos/'+repo
 info=json.loads(fetch(base,'repository.json'))
 commit=json.loads(fetch(base+'/commits/'+branch,'commit.json'));rev=commit['sha']
 tree=json.loads(fetch(base+'/git/trees/'+rev+'?recursive=1','tree.json'))
 assert not tree.get('truncated',False)
 for name in ['README.md','lean-toolchain','lake-manifest.json','LICENSE']:
  fetch('https://raw.githubusercontent.com/'+repo+'/'+rev+'/'+name,name+'.txt',optional=True)
 keys=['modularcurve','gamma1','goodreduction','jacobian','tatespecial','neron','picard','eichler','satotate','automorph','galoisrep','symmetricpower']
 matches=[x['path'] for x in tree['tree'] if x['type']=='blob' and x['path'].endswith(('.lean','.md')) and any(k in x['path'].lower().replace('_','') for k in keys)]
 (root/'candidates.json').write_text(json.dumps(matches,indent=2)+'\n',encoding='utf-8')
 (root/'fetch-manifest.json').write_text(json.dumps(dict(recordedUTC=datetime.now(timezone.utc).isoformat(),repository=repo,branch=branch,revision=rev,commitDate=commit['commit']['committer']['date'],files=records,externalBuild=False,externalImport=False,productionMutation=False),indent=2)+'\n',encoding='utf-8')
 return dict(repository=repo,branch=branch,revision=rev,commitDate=commit['commit']['committer']['date'],treeFiles=len(tree['tree']),candidateCount=len(matches))
with ThreadPoolExecutor(max_workers=3) as ex:
 futures=[ex.submit(review,t) for t in [('CBirkbeck/AINTLIB','main'),('CBirkbeck/AINTLIB','dev/modular-curves'),('facebookresearch/atlas-lean','main')]]
 for f in futures:
  try: print(json.dumps(f.result()),flush=True)
  except Exception as e: print(json.dumps(dict(error=str(e))),flush=True)
