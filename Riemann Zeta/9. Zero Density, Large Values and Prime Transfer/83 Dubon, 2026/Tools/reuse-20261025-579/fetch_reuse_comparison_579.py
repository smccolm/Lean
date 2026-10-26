from pathlib import Path
import requests,json,hashlib,datetime,concurrent.futures
p=Path(r'E:\Lean\.tmp\dubon83\reuse-20261025-579')
repo='anthropics/fermats-last-theorem';stem=repo.replace('/','__')
meta=requests.get('https://api.github.com/repos/'+repo,timeout=30).json()
c=requests.get('https://api.github.com/repos/'+repo+'/commits/'+meta['default_branch'],timeout=30);c.raise_for_status();commit=c.json()
t=requests.get('https://api.github.com/repos/'+repo+'/git/trees/'+commit['sha'],params={'recursive':1},timeout=30);t.raise_for_status();tree=t.json()
for suffix,data in [('repo',meta),('commit',commit),('tree',tree)]:
 f=p/(stem+'-'+suffix+'.json');assert not f.exists();f.write_text(json.dumps(data,indent=2))
print(json.dumps({'repo':repo,'sha':commit['sha'],'date':commit['commit']['committer']['date'],'truncated':tree.get('truncated')}))
choices={
'ImperialCollegeLondon/FLT':['README.md','lean-toolchain','lake-manifest.json','FLT/Assumptions/README.md','FLT/GaloisRepresentation/Automorphic.lean','FLT/GaloisRepresentation/HardlyRamified/Lift.lean'],
'roed314/gq2':['formalizations/axioms/index.html'],
'anr-false/anr-false.github.io':['index.html'],
'n-yamaguchi-0729/NYLL':['Nyll/SawinTotallyRealTowers/UnramifiedProPRelationRank/Radical/FinitePlaceCyclotomicLocalDuality.lean','Nyll/ValuedFieldTheory/Valuation/Subring/Residue/WittVectorValuationSubringResidueFieldEquiv.lean'],
'anthropics/fermats-last-theorem':['P2M/Sol/S_CuspForm_exists_galoisRep_of_point.lean','P2M/Sol/S_PDivisibleGroup_exists_basis_padicComplex_tateModule_eq_cyclotomicCharacter_pow_smul_of_hasDimension_of_ringOfIntegers.lean','P2M/Sol/S_groupCohomology_exists_localDualityPackage_res_dualTwist_extArithLoc.lean','LICENSE']}
rows=[]
for repo,paths in choices.items():
 stem=repo.replace('/','__');rev=json.loads((p/(stem+'-commit.json')).read_text())['sha']
 tree=json.loads((p/(stem+'-tree.json')).read_text())['tree'];entries={e['path']:e for e in tree if e['type']=='blob'}
 for path in paths:
  if path not in entries:print('missing',repo,path);continue
  rows.append((repo,rev,path,entries[path]['sha']))
def fetch(row):
 repo,rev,path,blob=row
 url='https://raw.githubusercontent.com/'+repo+'/'+rev+'/'+path
 r=requests.get(url,timeout=40);r.raise_for_status()
 actual=hashlib.sha1(b'blob '+str(len(r.content)).encode()+b'\0'+r.content).hexdigest();assert actual==blob
 dest=p/repo.replace('/','__')/(path+'.txt');dest.parent.mkdir(parents=True,exist_ok=True);assert not dest.exists();dest.write_bytes(r.content)
 return dict(repo=repo,commit=rev,path=path,url=url,snapshot=str(dest.relative_to(p)),sha256=hashlib.sha256(r.content).hexdigest().upper(),gitBlob=blob,bytes=len(r.content))
with concurrent.futures.ThreadPoolExecutor(max_workers=5) as pool:result=list(pool.map(fetch,rows))
f=p/'refresh-source-snapshots.json';assert not f.exists();f.write_text(json.dumps(dict(fetchedUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),files=result),indent=2))
print('Saved',len(result),'verified source snapshots')
