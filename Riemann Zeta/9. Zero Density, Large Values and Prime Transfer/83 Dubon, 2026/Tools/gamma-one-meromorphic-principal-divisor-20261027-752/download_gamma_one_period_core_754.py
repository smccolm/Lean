from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,urllib.request
s=Path(__file__).parent;o=s/'gamma-one-period-core-reuse-754';assert not o.exists();o.mkdir()
rev='6e837e75355538c7f80bab5b956861e86c4eacc2'
names=['S_ModularCurve_multiplier_eq_exp_of_periodAlongOf_add_petersson_mem_periodLatticeOf','S_ModularCurve_LevelN_twelve_mul_add_mul_index_le_genusFF','S_ModularCurve_LevelN_exists_linearMap_regularDifferentials_cuspForm_injective']
rows=[]
for n in names:
 path='P2M/Sol/'+n+'.lean';url='https://raw.githubusercontent.com/anthropics/fermats-last-theorem/'+rev+'/'+path
 req=urllib.request.Request(url,headers={'User-Agent':'Dubon-Lean-reuse-research'})
 try:
  with urllib.request.urlopen(req,timeout=45) as response: data=response.read()
  assert data and b'theorem solution' in data
  f=o/(n+'.lean.txt');f.write_bytes(data)
  row=dict(path=path,url=url,file=str(f),bytes=len(data),sha256=hashlib.sha256(data).hexdigest().upper(),gitBlob=hashlib.sha1(('blob '+str(len(data))+'\0').encode()+data).hexdigest(),retrievedUTC=datetime.now(timezone.utc).isoformat())
  rows.append(row)
 except Exception as e:
  (o/'download-failure.json').write_text(json.dumps(dict(url=url,error=str(e),completed=rows),indent=2)+'\n',encoding='utf-8');raise
(o/'manifest.json').write_text(json.dumps(dict(repository='anthropics/fermats-last-theorem',revision=rev,license='Apache-2.0',externalImport=False,externalClosureBuilt=False,files=rows),indent=2)+'\n',encoding='utf-8')
print(json.dumps([dict(file=Path(x['file']).name,bytes=x['bytes'],sha256=x['sha256']) for x in rows]))
