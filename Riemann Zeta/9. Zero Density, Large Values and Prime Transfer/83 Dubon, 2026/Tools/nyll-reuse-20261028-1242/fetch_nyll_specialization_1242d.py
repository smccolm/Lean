from pathlib import Path
from datetime import datetime,timezone
from urllib.request import Request,urlopen
from concurrent.futures import ThreadPoolExecutor
import json,hashlib
p=Path(__file__).parent/'nyll-reuse-1242b'
rev=json.loads((p/'fetch-manifest.json').read_text())['revision']
names=['Nyll/AnabelianGeometry/WeightFiltration/'+n+'.lean' for n in [
 'TorsionSpecialization','TorsionSpecializationWeights','TorsionTateSpecialization',
 'PicardSpecializationWeights','HenselianFrobeniusLift']]
names += ['Nyll/EtaleFundamentalGroups/GeometricFiber/HenselianSpecializationAction.lean']
def fetch(name):
 url='https://raw.githubusercontent.com/n-yamaguchi-0729/NYLL/'+rev+'/'+name
 f=p/(name+'.txt');assert not f.exists()
 data=urlopen(Request(url,headers={'User-Agent':'Dubon-proof-reuse-review'}),timeout=40).read()
 f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(data)
 return dict(url=url,path=name+'.txt',sha256=hashlib.sha256(data).hexdigest().upper(),bytes=len(data))
with ThreadPoolExecutor(max_workers=4) as pool:rows=list(pool.map(fetch,names))
out=p/'specialization-fetch-manifest-1242d.json';assert not out.exists()
out.write_text(json.dumps(dict(recordedUTC=datetime.now(timezone.utc).isoformat(),revision=rev,files=rows,externalBuild=False,externalImport=False,productionMutation=False),indent=2)+'\n')
print(json.dumps(dict(files=len(rows),bytes=sum(x['bytes'] for x in rows),revision=rev)))
