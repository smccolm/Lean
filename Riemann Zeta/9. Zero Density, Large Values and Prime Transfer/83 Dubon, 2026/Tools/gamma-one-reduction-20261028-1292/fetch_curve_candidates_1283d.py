from pathlib import Path
from datetime import datetime,timezone
from urllib.request import Request,urlopen
import json,hashlib
p=Path(__file__).parent/'curve-reuse-1283b'/'CBirkbeck--AINTLIB--main'
repo='CBirkbeck/AINTLIB';rev=json.loads((p/'commit.json').read_text(encoding='utf-8'))['sha']
names=['projects/ModularCurves/ModularCurves/ModularCurve/YOneAssembly.lean',
 'projects/ModularCurves/ModularCurves/ModularCurve/YOneAtlasClassify.lean',
 'projects/ModularCurves/ModularCurves/WeilPairing/KMDataset.lean',
 'projects/ModularCurves/ModularCurves/WeilPairing/KMCompatibility.lean']
records=[]
for name in names:
 url='https://raw.githubusercontent.com/'+repo+'/'+rev+'/'+name
 data=urlopen(Request(url,headers={'User-Agent':'Dubon-proof-reuse-review'}),timeout=40).read()
 f=p/(name+'.txt');f.parent.mkdir(parents=True,exist_ok=True);assert not f.exists();f.write_bytes(data)
 records.append(dict(url=url,path=name+'.txt',sha256=hashlib.sha256(data).hexdigest().upper(),bytes=len(data)))
out=p/'candidate-fetch-manifest-1283d.json';assert not out.exists()
out.write_text(json.dumps(dict(recordedUTC=datetime.now(timezone.utc).isoformat(),revision=rev,files=records,externalBuild=False,externalImport=False),indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(repository=repo,files=len(records),bytes=sum(x['bytes'] for x in records))))
