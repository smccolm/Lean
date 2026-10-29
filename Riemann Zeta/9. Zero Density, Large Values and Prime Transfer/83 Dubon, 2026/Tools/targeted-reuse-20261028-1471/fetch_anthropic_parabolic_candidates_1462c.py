from pathlib import Path
from datetime import datetime,timezone
from urllib.request import Request,urlopen
from concurrent.futures import ThreadPoolExecutor
import json,hashlib
s=Path(__file__).parent
base=s/'anthropic-parabolic-tree-1462'
review=json.loads((base/'review-manifest.json').read_text(encoding='utf-8'))
tree=json.loads((base/'sol-tree.json').read_text(encoding='utf-8'));assert not tree.get('truncated',False)
names=['S_CohCarrier_exists_linearMap_baseChange_parabolicHoms_top_comp_eq_comp_heckeTL_restrict_baseChange','S_CohCarrier_exists_perfect_selfAdjoint_degeneracyAdjoint_pairing_parabolicHoms','S_ModularCurve_CupPairing_exists_isParabolicHom_eq_sub_of_forall_finsum_eq_zero','S_ModularCurve_Period_exists_perfectPairing_parabolicHoms_baseChange','S_LevelRaising_exists_parabolicPairings_perfect_mod_three','S_HeckeEis_exists_coeffH1par_map_of_equivariant_retraction','S_HeckeEis_exists_coeffH1_restrict_injective_range_iff_equivariant_heckeT_of_charZero','S_HeckeEis_exists_coeffH1par_int_modp_eigenclass_of_eigenform','S_HeckeEis_exists_eq_prime_smul_of_coeffH1par_map_eq_zero','S_HeckeEis_existsUnique_coeffCocycles_sl2z_apply_S_ST_eq','S_groupCohomology_subsingleton_H1_dual_traceZero_of_toMatrix_eq_conj_specialLinearGroup_map','S_IsFreeGroup_surjective_transfer_and_transfer_eq_one_iff_mem_closure']
known={x['path'] for x in tree['tree']};assert all(n+'.lean' in known for n in names)
out=s/'anthropic-parabolic-candidates-1462c';out.mkdir(exist_ok=False)
def fetch(n):
 path='P2M/Sol/'+n+'.lean';url='https://raw.githubusercontent.com/anthropics/fermats-last-theorem/'+review['revision']+'/'+path
 data=urlopen(Request(url,headers={'User-Agent':'Dubon-proof-reuse-review'}),timeout=45).read()
 f=out/(n+'.lean.txt')
 with f.open('xb') as h:h.write(data)
 return dict(path=path,local=str(f),url=url,sha256=hashlib.sha256(data).hexdigest().upper(),bytes=len(data))
with ThreadPoolExecutor(max_workers=3) as ex:rows=list(ex.map(fetch,names))
(out/'fetch-manifest.json').write_text(json.dumps(dict(recordedUTC=datetime.now(timezone.utc).isoformat(),repository=review['repository'],revision=review['revision'],files=rows,externalBuild=False,externalImport=False,productionMutation=False),indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(files=len(rows),bytes=sum(r['bytes'] for r in rows),revision=review['revision'])))
