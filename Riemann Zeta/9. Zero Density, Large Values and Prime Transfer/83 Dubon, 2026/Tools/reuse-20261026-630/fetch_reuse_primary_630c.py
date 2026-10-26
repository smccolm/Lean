from pathlib import Path
import requests,json,hashlib,datetime,concurrent.futures
p=Path(r'E:\Lean\.tmp\dubon83')
out=p/'reuse-primary-followup-630c';assert not out.exists();out.mkdir()
heads={r['repo']:r['head'] for r in json.loads((p/'reuse-head-refresh-630b/manifest.json').read_text())['repos']}
items=[
 ('dozenalist/ModularFormsMod','ModularFormsMod/ModularFormMod/Hecke.lean'),
 ('dozenalist/ModularFormsMod','ModularFormsMod/ModularFormOver/Hecke.lean'),
 ('dozenalist/ModularFormsMod','lean-toolchain'),
 ('dozenalist/ModularFormsMod','lake-manifest.json'),
 ('leanprover-community/mathlib4','Mathlib/NumberTheory/HeckeRing/Defs.lean'),
 ('teal-sea/zeta-lab','lean/ZetaLean/FiniteFieldTrace.lean'),
 ('openai/math','lean/formalization.yaml'),
 ('openai/math','lean/docs/014.md')]
def get(url):
 r=requests.get(url,timeout=45);r.raise_for_status();return r
def fetch(z):
 repo,path=z;commit=heads[repo]
 meta=get('https://api.github.com/repos/'+repo+'/contents/'+path+'?ref='+commit).json()
 url='https://raw.githubusercontent.com/'+repo+'/'+commit+'/'+path
 b=get(url).content
 git=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert git==meta['sha']
 f=out/repo.replace('/','__')/(path+'.txt');f.parent.mkdir(parents=True,exist_ok=True);assert not f.exists();f.write_bytes(b)
 return dict(repo=repo,path=path,commit=commit,url=url,snapshot=str(f.relative_to(out)),gitBlob=git,sha256=hashlib.sha256(b).hexdigest().upper(),bytes=len(b))
rows=[]
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
 fs={pool.submit(fetch,z):z for z in items}
 for f in concurrent.futures.as_completed(fs):
  try:rows.append(f.result())
  except Exception as e:rows.append(dict(repo=fs[f][0],path=fs[f][1],error=str(e)))
repo='openai/math';tree=heads[repo]
steps=[]
for segment in ['lean','OAI','NumberTheory']:
 data=get('https://api.github.com/repos/'+repo+'/git/trees/'+tree).json()
 assert not data.get('truncated')
 steps.append(dict(sha=tree,segment=segment,tree=data))
 tree=next(x['sha'] for x in data['tree'] if x['path']==segment and x['type']=='tree')
data=get('https://api.github.com/repos/'+repo+'/git/trees/'+tree+'?recursive=1').json()
(out/'openai-number-theory-tree.json').write_text(json.dumps(dict(repo=repo,commit=heads[repo],steps=steps,result=data),indent=2)+'\n',encoding='utf-8')
(out/'snapshots.json').write_text(json.dumps(dict(retrievedUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),files=rows),indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(files=len(rows),errors=[r for r in rows if 'error' in r],numberTheoryFiles=len(data['tree']),truncated=data.get('truncated'))))
