from pathlib import Path
import json,urllib.request,hashlib
p=Path(r'E:\Lean\.tmp\dubon83');a=p/'reuse-head-refresh-741'
rows=json.loads((a/'manifest.json').read_text())['repositories']
out=[]
for row in rows:
 if not row['changed']:continue
 repo=row['repository'];url='https://api.github.com/repos/'+repo+'/compare/'+row['previousHead']+'...'+row['head']
 req=urllib.request.Request(url,headers={'User-Agent':'Dubon-Lean-reuse-research','Accept':'application/vnd.github+json'})
 b=urllib.request.urlopen(req,timeout=30).read();f=a/(repo.replace('/','__')+'-compare.json');assert not f.exists();f.write_bytes(b)
 v=json.loads(b)
 record=dict(repository=repo,url=url,status=v['status'],aheadBy=v['ahead_by'],totalCommits=v['total_commits'],
  files=[dict(path=x['filename'],status=x['status'],additions=x['additions'],deletions=x['deletions'],blobSha=x['sha']) for x in v.get('files',[])],
  snapshot=str(f),sha256=hashlib.sha256(b).hexdigest().upper())
 out.append(record);print(json.dumps(record),flush=True)
with (a/'comparisons.json').open('x',encoding='utf-8') as f:json.dump(out,f,indent=2);f.write('\n')
