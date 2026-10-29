from pathlib import Path
from datetime import datetime,timezone
from urllib.request import Request,urlopen
from concurrent.futures import ThreadPoolExecutor
import json,hashlib
s=Path(__file__).parent
base=s/'anthropic-parabolic-tree-1462'
review=json.loads((base/'review-manifest.json').read_text(encoding='utf-8'))
tree=json.loads((base/'sol-tree.json').read_text(encoding='utf-8'));assert not tree.get('truncated',False)
names=['S_ModularCurve_finrank_gammaH_le_finrank_gammaH_residueField_of_not_dvd','S_ModularCurve_genusFF_gammaH_residueField_eq_of_not_dvd','S_ModularCurve_index_gammaH_le_finrank_adjoin_jqModC_qExpFunctionFieldC_residueField','S_ModularCurve_index_gammaH_le_finrank_adjoin_jqModC_qExpFunctionFieldC_residueField_comap','S_ModularCurve_exists_transcendental_and_reductionInputsQExpModL_gammaH_of_not_dvd','S_CohCarrier_exists_galoisModule_parabolicHoms_to_dual_charInvolution_frobenius','S_ModularCurve_exists_heckeEquivariant_parabolicHoms_to_dual_tateModule_jH_charInvolution']
known={x['path'] for x in tree['tree']};assert all(n+'.lean' in known for n in names)
out=s/'anthropic-gamma-one-geometry-1463b';out.mkdir(exist_ok=False)
def fetch(n):
 path='P2M/Sol/'+n+'.lean';url='https://raw.githubusercontent.com/anthropics/fermats-last-theorem/'+review['revision']+'/'+path
 data=urlopen(Request(url,headers={'User-Agent':'Dubon-proof-reuse-review'}),timeout=45).read()
 f=out/(n+'.lean.txt')
 with f.open('xb') as h:h.write(data)
 return dict(path=path,local=str(f),url=url,sha256=hashlib.sha256(data).hexdigest().upper(),bytes=len(data))
with ThreadPoolExecutor(max_workers=3) as ex:rows=list(ex.map(fetch,names))
(out/'fetch-manifest.json').write_text(json.dumps(dict(recordedUTC=datetime.now(timezone.utc).isoformat(),repository=review['repository'],revision=review['revision'],files=rows,externalBuild=False,externalImport=False,productionMutation=False),indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(files=len(rows),bytes=sum(r['bytes'] for r in rows),revision=review['revision'])))
