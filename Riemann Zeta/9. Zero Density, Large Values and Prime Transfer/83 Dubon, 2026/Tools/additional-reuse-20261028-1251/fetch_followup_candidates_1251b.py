from pathlib import Path
from datetime import datetime,timezone
from urllib.request import Request,urlopen
import json,hashlib
p=Path(__file__).parent/'followup-reuse-1251'
targets={'F-Najman/normalizer-lean':['NormalizerDelta/StatementsXN.lean','NormalizerLean/Defs.lean'],
 'tomdif/eml-lean':['EML/EichlerIntegral.lean','EML/HeckeAction.lean']}
for repo,names in targets.items():
 root=p/repo.replace('/','--');rev=json.loads((root/'commit.json').read_text())['sha']
 records=[]
 for name in names:
  url='https://raw.githubusercontent.com/'+repo+'/'+rev+'/'+name
  data=urlopen(Request(url,headers={'User-Agent':'Dubon-proof-reuse-review'}),timeout=40).read()
  f=root/(name+'.txt');f.parent.mkdir(parents=True,exist_ok=True);assert not f.exists();f.write_bytes(data)
  records.append(dict(url=url,path=name+'.txt',sha256=hashlib.sha256(data).hexdigest().upper(),bytes=len(data)))
 out=root/'candidate-fetch-manifest-1251b.json';assert not out.exists()
 out.write_text(json.dumps(dict(recordedUTC=datetime.now(timezone.utc).isoformat(),revision=rev,files=records,externalBuild=False,externalImport=False),indent=2)+'\n',encoding='utf-8')
 print(json.dumps(dict(repository=repo,files=len(records),bytes=sum(x['bytes'] for x in records))))
