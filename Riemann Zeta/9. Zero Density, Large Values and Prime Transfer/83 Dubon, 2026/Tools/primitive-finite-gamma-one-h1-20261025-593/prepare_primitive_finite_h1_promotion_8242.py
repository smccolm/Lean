from pathlib import Path
import ast,json,re,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
oldroute=json.loads((p/'primitive-finite-h1-promotion-route-587.json').read_text())
digests=dict(oldroute['receipts'])
receipt=p/'source-primitive-permutation-operator-character-7-scratch-receipt.json'
digests[receipt.name]=sha(receipt)
certs=[json.loads((p/f).read_text()) for f in digests]
assert all(sha(p/f)==h for f,h in digests.items())
assert (sum(len(c['modules']) for c in certs),sum(len(c['queries']) for c in certs),sum(len(c['theoremRegistrations']) for c in certs),sum(len(c['constructionRegistrations']) for c in certs),sum(c['exhaustiveTheorems'] for c in certs),sum(c['requiredProofValueEdges'] for c in certs))==(29,76,53,23,179,124)
dependency=oldroute['dependency']+' -> canonical surjection from actual finite permutation Hecke operators to the original finite operator image'
discharged=oldroute['discharged']+' The full permutation H1 Hecke image is finite and canonically surjects onto the original finite tensor-operator image. Every relation is transferred using proved evaluation surjectivity, additive Hecke-word naturality and the exact original integral reduction kernel. Composing this surjection with the same original finite character gives permutation Hecke characters at every positive power of each prime greater than three, with whole-word pullback and exact original Fourier values. No relation or character-lifting premise is retained.'
boundary=oldroute['remaining']
route=oldroute['route']+' The existing general additive Hecke-word intertwiner also gives the canonical permutation operator quotient; a new word-induction development and integral lifting of arbitrary residual H1 are unnecessary.'
status='The original-form finite H1 and permutation Hecke-character chain passes 179 exhaustive scratch checks and 76 explicit axiom queries across 29 modules, with sixteen linters per module and zero diagnostics. Six declaration-value audits verify 124 required dependencies. Production aggregate, focused audit and sequential foundation/paper verification of the 8,242-module scope are pending.'
def output(name,s):
 f=p/name;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
rp=p/'primitive-finite-permutation-h1-promotion-route-590.json'
output(rp.name,json.dumps(dict(scope=590,scopeIds=[582,583,584,585,586,588],receipts=digests,dependency=dependency,discharged=discharged,remaining=boundary,route=route,precedingCanonicalScope=8213,mathematicalSource=oldroute['mathematicalSource'],rootPinsChanged=False,proofLimitsChanged=False,externalImport=False,supersededUnexecutedPreparation=8235,reason='The additional audited permutation-character bridge is ready before the previous assembled verification finishes. Combine it with the still-unexecuted 8235 promotion, preserving all receipts and avoiding a redundant full verification cycle.'),indent=2)+'\n')
def transform(s):
 return s.replace('primitive-finite-h1-promotion-route-587.json',rp.name).replace('Tools/primitive-finite-h1-20261025-587','Tools/primitive-finite-permutation-h1-20261025-590').replace('8,235','8,242').replace('8235','8242')
s=transform((p/'integrate_source_primitive_finite_h1_realization_8235.py').read_text(encoding='utf-8'))
s=re.sub(r'^digests = .+$',lambda _:'digests = '+repr(digests),s,flags=re.M)
s=s.replace('(22, 22, 56, 39, 17)','(29, 29, 76, 53, 23)').replace('count == 126','count == 179').replace('"increment": 22, "queries": 56','"increment": 29, "queries": 76')
for key,value in [('dependency',dependency),('discharged',discharged),('boundary',boundary),('route',route),('status',status)]:
 s=re.sub(r'^'+key+r' = .+$',lambda _,key=key,value=value:key+' = '+repr(value),s,flags=re.M)
extra=[f.name for f in p.iterdir() if f.is_file() and f.suffix in ['.py','.json','.lean','.log','.exit'] and (re.search(r'(?<!\d)588[a-z]?\.',f.name) or f.name.startswith(('SourcePrimitivePermutationOperatorCharacterAudit','SourcePrimitivePermutationOperatorCharacterDependencyAudit','source-primitive-permutation-operator-character-7-audit-config')))]
extra+=['primitive-finite-h1-promotion-route-587.json','primitive-finite-h1-preexecution-review-8235.json']
for f in p.iterdir():
 if f.is_file() and re.search(r'8235\.(py|ps1)$',f.name):extra.append(f.name)
s=s.replace('for folder in [', 'evidence += [p/name for name in '+repr(sorted(set(extra)))+']\nfor folder in [',1)
s=s.replace('Compatible original finite H1 operator characters and congruence-stabilizer comparison proved;','Compatible original finite H1 and permutation Hecke characters with a canonical surjection and congruence-stabilizer comparison proved;')
output('integrate_source_primitive_finite_h1_realization_8242.py',s)
for stem in ['prepare_primitive_finite_h1_realization_production_ownership','prepare_primitive_finite_h1_realization_scratch_ownership','compare_primitive_finite_h1_realization_ownership','record_source_primitive_finite_h1_realization','prepare_primitive_finite_h1_realization_global_ownership']:
 s=transform((p/(stem+'_8235.py')).read_text(encoding='utf-8'))
 s=re.sub(r'\b126\b','179',s)
 if stem.startswith('compare'):
  s=s.replace('len(names)==len(certs)==5','len(names)==len(certs)==6').replace('All 22 mathematical','All 29 mathematical')
 if stem.startswith('record'):
  s=s.replace('== 22','== 29').replace('"incrementModules": 22','"incrementModules": 29').replace('"linterScopes": 22','"linterScopes": 29')
  s=s.replace('== 2244','== 2250').replace('== 23760','== 23774')
  s=s.replace('Five declaration-value audits verify 93 required dependencies.','Six declaration-value audits verify 124 required dependencies.')
  s=s.replace('16/22','16/20').replace('DUB-17-22','DUB-17-20')
 output(stem+'_8242.py',s)
for stem in ['build_primitive_finite_h1_realization','verify_primitive_finite_h1_realization']:
 output(stem+'_8242.ps1',transform((p/(stem+'_8235.ps1')).read_text(encoding='utf-8')))
output('archive_primitive_finite_h1_canonical_8242.py',transform((p/'archive_primitive_finite_h1_canonical_8235.py').read_text(encoding='utf-8')))
scripts=[f for f in p.iterdir() if re.search(r'8242\.(py|ps1)$',f.name)]
for f in scripts:
 if f.suffix=='.py':ast.parse(f.read_text(encoding='utf-8'))
 assert '16/22' not in f.read_text(encoding='utf-8') and 'DUB-17-22' not in f.read_text(encoding='utf-8')
review=dict(status='Prepared; no production mutation. Must wait for 8213 canonical PASS and its archive.',route=rp.name,routeSha256=sha(rp),modules=29,queries=76,theorems=53,constructions=23,exhaustiveScratchChecks=179,proofValueEdges=124,scopes=6,fullGoal='20 acceptance gates unchanged; 16/20 and DUB-17--20 OPEN',supersededUnused8235=True,correction='Preexecution review caught stale 16/22 gate strings in the unused 8235 recorder caused by a broad numeric replacement. Fresh 8242 uses the unchanged 16/20 source contract. No 8235 integration, audit, or verification was executed.',receipts=digests,pythonAST='PASS',scripts=[dict(path=str(f),sha256=sha(f)) for f in scripts],archiveExtraFiles=len(set(extra)))
output('primitive-finite-h1-preexecution-review-8242.json',json.dumps(review,indent=2)+'\n')
print(json.dumps(dict(prepared=len(scripts),modules=29,queries=76,exhaustive=179,edges=124,routeSha256=sha(rp),productionMutation=False)))
