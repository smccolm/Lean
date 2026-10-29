from pathlib import Path
from datetime import datetime,timezone
from urllib.request import Request,urlopen
from concurrent.futures import ThreadPoolExecutor
import json,hashlib
p=Path(__file__).parent/'curve-reuse-1283b'
targets={
 'CBirkbeck/AINTLIB':[
 'projects/ModularCurves/docs/README.md',
 'projects/ModularCurves/ModularCurves/GroupScheme/NIsogeny.lean',
 'projects/ModularCurves/ModularCurves/WeilPairing/Basic.lean',
 'projects/ModularCurves/ModularCurves/Moduli/GammaOneNaiveRelRep.lean',
 'projects/ModularCurves/ModularCurves/Moduli/Representability.lean',
 'projects/ModularCurves/ModularCurves/Moduli/GammaHMaster.lean',
 'projects/LeanModularForms/LeanModularForms/HeckeRIngs/GL2/HeckeT_p_Gamma1.lean'],
 'facebookresearch/atlas-lean':[
 'MathlibExt/AlgebraicGeometry/EllipticCurve/GaloisRepresentation.lean',
 'MathlibExt/AlgebraicGeometry/EllipticCurve/NeronOggShafarevich.lean',
 'v1/Atlas/EllipticCurves/code/ModularCurves.lean',
 'v1/Atlas/ArithmeticGeometry/code/PicardGroup.lean',
 'v1/Atlas/AlgebraicGeometryI/code/DivisorsPicard.lean']}
def review(item):
 repo,names=item;root=p/(repo.replace('/','--')+'--main')
 rev=json.loads((root/'commit.json').read_text(encoding='utf-8'))['sha']; records=[]
 for name in names:
  url='https://raw.githubusercontent.com/'+repo+'/'+rev+'/'+name
  data=urlopen(Request(url,headers={'User-Agent':'Dubon-proof-reuse-review'}),timeout=40).read()
  f=root/(name+'.txt');f.parent.mkdir(parents=True,exist_ok=True);assert not f.exists();f.write_bytes(data)
  records.append(dict(url=url,path=name+'.txt',sha256=hashlib.sha256(data).hexdigest().upper(),bytes=len(data)))
 out=root/'candidate-fetch-manifest-1283c.json';assert not out.exists()
 out.write_text(json.dumps(dict(recordedUTC=datetime.now(timezone.utc).isoformat(),revision=rev,files=records,externalBuild=False,externalImport=False),indent=2)+'\n',encoding='utf-8')
 return dict(repository=repo,files=len(records),bytes=sum(x['bytes'] for x in records))
with ThreadPoolExecutor(max_workers=2) as ex:
 for result in ex.map(review,targets.items()): print(json.dumps(result),flush=True)
