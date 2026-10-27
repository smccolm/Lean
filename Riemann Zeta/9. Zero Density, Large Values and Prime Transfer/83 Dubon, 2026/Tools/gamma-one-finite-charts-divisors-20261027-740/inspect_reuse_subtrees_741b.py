from pathlib import Path
import json, urllib.request, hashlib
p=Path(r"E:\Lean\.tmp\dubon83\reuse-head-refresh-741")
rows=[]
def fetch(name,sha,recursive=False):
 url='https://api.github.com/repos/openai/math/git/trees/'+sha+('?recursive=1' if recursive else '')
 f=p/('openai__math-'+name+'-tree.json'); assert not f.exists()
 b=urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Dubon-Lean-reuse-research'}),timeout=60).read(); f.write_bytes(b);v=json.loads(b)
 rows.append(dict(path=str(f),url=url,sha256=hashlib.sha256(b).hexdigest().upper(),truncated=v.get('truncated'),entries=len(v['tree'])))
 print(json.dumps(rows[-1]),flush=True)
 return v['tree']
oai=fetch('OAI','e5a41abb72afe7111d5608308439bc1d66bab5a4')
for x in oai:
 if x['type']=='tree' and x['path'] in ['NumberTheory','AlgebraicGeometry']:
  tree=fetch(x['path'],x['sha'],True)
  if rows[-1]['truncated']:
   children=fetch(x['path']+'-children',x['sha'])
   for c in children:
    if c['type']=='tree': fetch(x['path']+'-'+c['path'],c['sha'],True)
with (p/'subtree-snapshots.json').open('x',encoding='utf-8') as f:json.dump(rows,f,indent=2);f.write('\n')
