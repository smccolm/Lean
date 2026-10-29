from pathlib import Path
from datetime import datetime,timezone
from urllib.request import Request,urlopen
from concurrent.futures import ThreadPoolExecutor
import json,hashlib
p=Path(__file__).parent
out=p/'lana-reuse-1432c';out.mkdir(exist_ok=False)
chosen={
 'lana-agents/elliptic-curves':['EllipticCurves/Reduction/GoodReductionCriterion.lean','EllipticCurves/Reduction/NeronOggShafarevich.lean','EllipticCurves/Torsion/StructureGeneral.lean'],
 'lana-agents/elliptic-reduction':['EllipticReduction/Basic.lean'],
 'lana-agents/tate-curves-theta':['TateCurvesTheta/TateCurve/TateUniformization.lean','TateCurvesTheta/TateCurve/WeierstrassIdentity.lean','TateCurvesTheta/Converse/ReductionType.lean'],
 'anthropics/fermats-last-theorem':['P2M/Sol/S_HeckeEis_exists_coeffH1par_projLineRepSL_equiv_parabolicHoms.lean','P2M/Sol/S_HeckeEis_exists_modularForm_coeffCocycles_sub_cocycle_mem_coeffParabolicCocycles.lean']}
tasks=[]
for repo,paths in chosen.items():
 if repo.startswith('lana-'):
  base=p/'lana-reuse-1432b'/(repo.replace('/','--')+'--main')
  rev=json.loads((base/'commit.json').read_text(encoding='utf-8'))['sha']
  tree=json.loads((base/'tree.json').read_text(encoding='utf-8'))
 else:
  rev='6e837e75355538c7f80bab5b956861e86c4eacc2'
  tree=json.loads((p/'reuse-head-refresh-630b/anthropics__fermats-last-theorem-tree.json').read_text(encoding='utf-8'))
 assert not tree.get('truncated',False)
 known={row['path'] for row in tree['tree']}
 for path in paths:
  assert path in known,path
  tasks.append((repo,rev,path))
def fetch(task):
 repo,rev,path=task
 url='https://raw.githubusercontent.com/'+repo+'/'+rev+'/'+path
 data=urlopen(Request(url,headers={'User-Agent':'Dubon-proof-reuse-review'}),timeout=40).read()
 dest=out/repo.replace('/','--')/(path+'.txt');dest.parent.mkdir(parents=True,exist_ok=True)
 with dest.open('xb') as f:f.write(data)
 return dict(repository=repo,revision=rev,path=path,url=url,local=str(dest),sha256=hashlib.sha256(data).hexdigest().upper(),bytes=len(data))
with ThreadPoolExecutor(max_workers=3) as ex:rows=list(ex.map(fetch,tasks))
(out/'fetch-manifest.json').write_text(json.dumps(dict(recordedUTC=datetime.now(timezone.utc).isoformat(),files=rows,externalBuild=False,externalImport=False,productionMutation=False),indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(files=len(rows),manifest=str(out/'fetch-manifest.json'))))
