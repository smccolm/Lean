from pathlib import Path
import ast,json,re,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
old=json.loads((p/'primitive-finite-permutation-h1-promotion-route-590.json').read_text())
digests=dict(old['receipts'])
certfile=p/'source-gamma-one-cover-6-scratch-receipt.json';digests[certfile.name]=sha(certfile)
certs=[json.loads((p/f).read_text()) for f in digests]
assert all(sha(p/f)==h for f,h in digests.items())
assert tuple(sum(len(c[k]) for c in certs) for k in ['modules','queries','theoremRegistrations','constructionRegistrations'])==(35,96,68,28)
assert (sum(c['exhaustiveTheorems'] for c in certs),sum(c['requiredProofValueEdges'] for c in certs))==(205,157)
dependency=old['dependency']+' -> exact finite-index Gamma1 cover and surjective constant-coefficient H1 realization'
discharged=old['discharged']+' The exact Gamma1(Q*N^2) diagonal map is injective, has finite-index image in the original Gamma0(Q), fixes the actual binary vectors modulo N and dominates their actual orbit stabilizers. Native coinduction with faithful restriction, the existing Gamma0 H2 vanishing, Shapiro and group reindexing give a surjective constant-coefficient Gamma1 H1 transfer. Every original integral binary H1 class modulo every positive power of every prime greater than three has an actual preimage.'
boundary='The Gamma1 transfer and transported stabilizer operators have not yet been identified with arithmetic geometric correspondences or the required Gamma1 Hecke-and-diamond actions. Geometric Galois realization of these finite characters, compatible original all-weight characteristic-zero association, required local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain required. No eigenvector lift, arithmetic Galois action or characteristic-zero deformation point is claimed from the finite constructions alone. 16/20; DUB-17--20 OPEN.'
route=old['route']+' The follow-up inspection of five fixed-revision Gamma1 sources identifies a useful arithmetic curve family but retains its characteristic-zero character hypothesis. Existing local level raising, subgroup indices, coinduction, Shapiro and group reindexing prove the exact group and cohomology bridge without a new curve construction or new exact-sequence development.'
status='The original-form finite H1, permutation Hecke-character and Gamma1 realization chain passes 205 exhaustive scratch checks and 96 explicit axiom queries across 35 modules, with sixteen linters per module and zero diagnostics. Seven declaration-value audits verify 157 required dependencies. Production aggregate, focused audit and sequential foundation/paper verification of the 8,248-module scope are pending.'
def output(name,s):
 f=p/name;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
rp=p/'primitive-finite-gamma-one-h1-promotion-route-593.json'
output(rp.name,json.dumps(dict(scope=593,scopeIds=[582,583,584,585,586,588,591],receipts=digests,dependency=dependency,discharged=discharged,remaining=boundary,route=route,precedingCanonicalScope=8213,mathematicalSource=old['mathematicalSource'],rootPinsChanged=False,proofLimitsChanged=False,externalImport=False,supersededUnexecutedPreparations=[8235,8242],reason='The exact Gamma1/cohomology bridge passed before the prior assembled verification finished. One combined promotion preserves every scratch audit and avoids redundant intermediate assembled verification.'),indent=2)+'\n')
def transform(s):
 return s.replace('primitive-finite-permutation-h1-promotion-route-590.json',rp.name).replace('Tools/primitive-finite-permutation-h1-20261025-590','Tools/primitive-finite-gamma-one-h1-20261025-593').replace('8,242','8,248').replace('8242','8248')
s=transform((p/'integrate_source_primitive_finite_h1_realization_8242.py').read_text(encoding='utf-8'))
s=re.sub(r'^digests = .+$',lambda _:'digests = '+repr(digests),s,flags=re.M)
s=s.replace('(29, 29, 76, 53, 23)','(35, 35, 96, 68, 28)').replace('count == 179','count == 205').replace('"increment": 29, "queries": 76','"increment": 35, "queries": 96')
for k,v in [('dependency',dependency),('discharged',discharged),('boundary',boundary),('route',route),('status',status)]:
 s=re.sub(r'^'+k+r' = .+$',lambda _,k=k,v=v:k+' = '+repr(v),s,flags=re.M)
extra=[f.name for f in p.iterdir() if f.is_file() and f.suffix in ['.py','.ps1','.json','.lean','.log','.exit'] and (re.search(r'(?<!\d)(589|591|8242)[a-z]?\.',f.name) or f.name.startswith(('SourceGammaOneCoverAudit','SourceGammaOneCoverDependencyAudit','source-gamma-one-cover-6-audit-config')))]
extra+=['primitive-finite-permutation-h1-promotion-route-590.json']
s=s.replace('for folder in [','evidence += [p/name for name in '+repr(sorted(set(extra)))+']\nevidence += [f for f in (p/"gamma1-geometric-reuse-589").rglob("*") if f.is_file()]\nfor folder in [',1)
oldtarget="    target=r/archive_rel/(source.parent.name if source.parent != p else '')/(source.name+('.txt' if source.suffix=='.lean' else ''))"
assert oldtarget in s
s=s.replace(oldtarget,"    if source.is_relative_to(p/'gamma1-geometric-reuse-589'):\n        target=r/archive_rel/source.relative_to(p)\n    else:\n    "+oldtarget)
s=s.replace('with a canonical surjection and congruence-stabilizer comparison proved;','with a canonical surjection, congruence-stabilizer comparison and exact constant-coefficient Gamma1 realization proved;')
output('integrate_source_primitive_finite_h1_realization_8248.py',s)
for stem in ['prepare_primitive_finite_h1_realization_production_ownership','prepare_primitive_finite_h1_realization_scratch_ownership','compare_primitive_finite_h1_realization_ownership','record_source_primitive_finite_h1_realization','prepare_primitive_finite_h1_realization_global_ownership']:
 s=transform((p/(stem+'_8242.py')).read_text(encoding='utf-8'))
 s=re.sub(r'\b179\b','205',s)
 if stem.startswith('compare'):
  s=s.replace('len(names)==len(certs)==6','len(names)==len(certs)==7').replace('All 29 mathematical','All 35 mathematical')
 if stem.startswith('record'):
  s=s.replace('== 29','== 35').replace('"incrementModules": 29','"incrementModules": 35').replace('"linterScopes": 29','"linterScopes": 35')
  s=s.replace('== 2250','== 2255').replace('== 23774','== 23789')
  s=s.replace('Six declaration-value audits verify 124 required dependencies.','Seven declaration-value audits verify 157 required dependencies.')
 output(stem+'_8248.py',s)
for stem in ['build_primitive_finite_h1_realization','verify_primitive_finite_h1_realization']:
 output(stem+'_8248.ps1',transform((p/(stem+'_8242.ps1')).read_text(encoding='utf-8')))
output('archive_primitive_finite_h1_canonical_8248.py',transform((p/'archive_primitive_finite_h1_canonical_8242.py').read_text(encoding='utf-8')))
scripts=[f for f in p.iterdir() if re.search(r'8248\.(py|ps1)$',f.name) and f.name!='prepare_primitive_finite_h1_promotion_8248.py']
for f in scripts:
 s=f.read_text(encoding='utf-8')
 if f.suffix=='.py':ast.parse(s)
 assert '16/22' not in s and 'DUB-17-22' not in s,f
review=dict(status='Prepared; require 8213 canonical PASS and archive before integration.',route=rp.name,routeSha256=sha(rp),modules=35,queries=96,theorems=68,constructions=28,exhaustiveScratchChecks=205,proofValueEdges=157,scopes=7,fullGoal='16/20; DUB-17--20 OPEN; all 20 acceptance gates unchanged.',supersededUnused=[8235,8242],receipts=digests,pythonAST='PASS for seven execution helpers',scripts=[dict(path=str(f),sha256=sha(f)) for f in scripts],sourceBodies='Audited bodies unchanged; only project imports qualified.',expectedConsumers=23789,expectedConstructions=2255,sourceScopes=[582,583,584,585,586,588,591],primaryGamma1Archive='Preserve the complete gamma1-geometric-reuse-589 relative paths so source manifest references remain valid.',productionMutation=False)
output('primitive-finite-h1-preexecution-review-8248.json',json.dumps(review,indent=2)+'\n')
print(json.dumps(dict(scripts=len(scripts),routeSha256=sha(rp),modules=35,queries=96,exhaustive=205,edges=157,productionMutation=False)))
