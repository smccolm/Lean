from pathlib import Path
from datetime import datetime,timezone
from urllib.request import Request,urlopen
from urllib.error import HTTPError
import json,hashlib
p=Path(__file__).parent/'followup-reuse-1251'
p.mkdir(exist_ok=False)
for repo in ['F-Najman/normalizer-lean','tomdif/eml-lean']:
 root=p/repo.replace('/','--');root.mkdir()
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
 commit=json.loads(fetch(base+'/commits/'+info['default_branch'],'commit.json'));rev=commit['sha']
 tree=json.loads(fetch(base+'/git/trees/'+rev+'?recursive=1','tree.json'))
 assert not tree.get('truncated',False)
 for name in ['README.md','lean-toolchain','lake-manifest.json','LICENSE']:
  fetch('https://raw.githubusercontent.com/'+repo+'/'+rev+'/'+name,name+'.txt',optional=True)
 matches=[x['path'] for x in tree['tree'] if x['type']=='blob' and any(k.lower() in x['path'].lower() for k in ['StatementsXN','StatementsX1','Eichler','Hecke','Galois','Reduction','Deligne','Shimura'])]
 (root/'candidates.json').write_text(json.dumps(matches,indent=2)+'\n',encoding='utf-8')
 (root/'fetch-manifest.json').write_text(json.dumps(dict(recordedUTC=datetime.now(timezone.utc).isoformat(),repository=repo,revision=rev,commitDate=commit['commit']['committer']['date'],files=records,externalBuild=False,externalImport=False,productionMutation=False),indent=2)+'\n',encoding='utf-8')
 print(json.dumps(dict(repository=repo,revision=rev,commitDate=commit['commit']['committer']['date'],treeFiles=len(tree['tree']),candidatePaths=matches)))
