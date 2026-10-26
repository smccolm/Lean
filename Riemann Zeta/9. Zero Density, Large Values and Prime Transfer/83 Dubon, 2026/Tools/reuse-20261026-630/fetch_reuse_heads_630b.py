from pathlib import Path
import requests,json,hashlib,datetime,concurrent.futures
out=Path(r'E:\Lean\.tmp\dubon83\reuse-head-refresh-630b')
assert not out.exists()
out.mkdir()
repos=['anthropics/fermats-last-theorem','ImperialCollegeLondon/FLT','dozenalist/ModularFormsMod','openai/math','leanprover-community/mathlib4','teal-sea/zeta-lab']
def fetch(repo):
 key=repo.replace('/','__')
 def get(suffix,label):
  url='https://api.github.com/repos/'+repo+suffix
  res=requests.get(url,headers={'Accept':'application/vnd.github+json'},timeout=45)
  res.raise_for_status();data=res.json()
  f=out/(key+'-'+label+'.json')
  assert not f.exists()
  f.write_text(json.dumps(data,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
  return data,dict(path=f.name,url=url,sha256=hashlib.sha256(f.read_bytes()).hexdigest().upper())
 meta,mr=get('','repo')
 commit,cr=get('/commits/'+meta['default_branch'],'commit')
 tree,tr=get('/git/trees/'+commit['sha']+'?recursive=1','tree')
 hits=[x['path'] for x in tree.get('tree',[]) if x['type']=='blob' and any(t in x['path'].lower() for t in ['satotate','sato_tate','sato-tate','automorph','galoisrep','modularity','hecke','deligne','symmetricpower','symmetric_power','formalization.yaml','ramanujan'])]
 return dict(repo=repo,head=commit['sha'],commitDate=commit['commit']['committer']['date'],defaultBranch=meta['default_branch'],license=meta.get('license'),treeTruncated=tree.get('truncated'),matches=hits,records=[mr,cr,tr])
rows=[]
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:
 futures={pool.submit(fetch,r):r for r in repos}
 for f in concurrent.futures.as_completed(futures):
  r=futures[f]
  try:
   z=f.result();rows.append(z);print(json.dumps(dict(repo=r,head=z['head'],date=z['commitDate'],hits=len(z['matches']),truncated=z['treeTruncated'])),flush=True)
  except Exception as e:
   rows.append(dict(repo=r,error=str(e)));print(json.dumps(dict(repo=r,error=str(e))),flush=True)
(out/'manifest.json').write_text(json.dumps(dict(retrievedUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),repos=rows),indent=2)+'\n',encoding='utf-8')
