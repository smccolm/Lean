from pathlib import Path
import requests,json,hashlib,datetime
p=Path(r'E:\Lean\.tmp\dubon83\reuse-20261025-579')
out=[]
for repo in ['n-yamaguchi-0729/NYLL','ImperialCollegeLondon/FLT','roed314/gq2','anr-false/anr-false.github.io']:
 stem=repo.replace('/','__')
 r=requests.get('https://api.github.com/repos/'+repo,timeout=30)
 if r.status_code!=200:print(repo,r.status_code);continue
 meta=r.json()
 c=requests.get('https://api.github.com/repos/'+repo+'/commits/'+meta['default_branch'],timeout=30);c.raise_for_status();commit=c.json()
 t=requests.get('https://api.github.com/repos/'+repo+'/git/trees/'+commit['sha'],params={'recursive':1},timeout=30);t.raise_for_status();tree=t.json()
 for suffix,data in [('repo',meta),('commit',commit),('tree',tree)]:
  f=p/(stem+'-'+suffix+'.json');assert not f.exists();f.write_text(json.dumps(data,indent=2))
 print(json.dumps({'repo':repo,'sha':commit['sha'],'date':commit['commit']['committer']['date'],'files':len(tree.get('tree',[])),'truncated':tree.get('truncated')}))
