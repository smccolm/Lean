from pathlib import Path
from datetime import datetime, timezone
import json, urllib.request, hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
a=p/'reuse-head-refresh-741'
assert not a.exists()
a.mkdir()
repos={'anthropics/fermats-last-theorem':'6e837e75355538c7f80bab5b956861e86c4eacc2',
 'ImperialCollegeLondon/FLT':'a3210204ad8876e851e32f73dd97d882bf1ccd0a',
 'dozenalist/ModularFormsMod':'bc16671d6781a26216b378773502ba5583845cbf',
 'dozenalist/LeanModularForms':'f737ca88e0887ecbaad3510b30e37042c243fd17',
 'leanprover-community/mathlib4':'8d14a32337a069dbae9b92875aeb697de357b5ac',
 'openai/math':'1581d4cbdd69a0faf34b2089614fe2a814316a6a',
 'teal-sea/zeta-lab':'558eee037f954989986abad4b25851d9a41604ca'}
rows=[]
for repo,old in repos.items():
 url='https://api.github.com/repos/'+repo+'/commits?per_page=1'
 req=urllib.request.Request(url,headers={'User-Agent':'Dubon-Lean-reuse-research','Accept':'application/vnd.github+json'})
 b=urllib.request.urlopen(req,timeout=30).read()
 f=a/(repo.replace('/','__')+'-head.json');f.write_bytes(b)
 v=json.loads(b)[0]
 row=dict(repository=repo,previousHead=old,head=v['sha'],changed=old!=v['sha'],
  commitDate=v['commit']['committer']['date'],url=v['html_url'],retrievedUTC=datetime.now(timezone.utc).isoformat(),
  snapshot=str(f),sha256=hashlib.sha256(b).hexdigest().upper())
 rows.append(row);print(json.dumps(row),flush=True)
with (a/'manifest.json').open('x',encoding='utf-8') as f:
 json.dump(dict(scope='Live default-branch head refresh after the October26 search. This checks new commits, not a new local build or proof audit of any external repository.',repositories=rows,rootPinsChanged=False,externalImport=False),f,indent=2);f.write('\n')
