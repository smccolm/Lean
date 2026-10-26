from pathlib import Path
import requests,json,hashlib,datetime
p=Path(r'E:\Lean\.tmp\dubon83\reuse-20261025-579')
p.mkdir(exist_ok=True)
s=requests.Session()
s.headers['User-Agent']='Dubon-Lean-reuse-review'
for repo in ['lioristhmus/ramanujan-petersson','mkaratarakis/CICM24_Deligne','mkaratarakis/Deligne','tianyipeng/fermats-last-theorem']:
 stem=repo.replace('/','__')
 r=s.get('https://api.github.com/repos/'+repo,timeout=25)
 if r.status_code!=200:print(repo,r.status_code);continue
 meta=r.json();branch=meta['default_branch']
 c=s.get('https://api.github.com/repos/'+repo+'/commits/'+branch,timeout=25)
 c.raise_for_status();commit=c.json()
 t=s.get('https://api.github.com/repos/'+repo+'/git/trees/'+commit['sha'],params={'recursive':'1'},timeout=25)
 t.raise_for_status();tree=t.json()
 for suffix,data in [('repo',meta),('commit',commit),('tree',tree)]:
  f=p/(stem+'-'+suffix+'.json');assert not f.exists();f.write_text(json.dumps(data,indent=2),encoding='utf-8')
 paths=[e['path'] for e in tree['tree'] if e['type']=='blob']
 print(json.dumps({'repo':repo,'sha':commit['sha'],'date':commit['commit']['committer']['date'],'license':(meta.get('license') or {}).get('spdx_id'),'files':len(paths),'selected':[x for x in paths if any(v in x.lower() for v in ['readme','toolchain','manifest','statement','deligne','galoisrep_of_point'])][:50]}))
