from pathlib import Path
import ast,json,re,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
spec=[
(592,'source-gamma-one-hecke-trace-7-scratch-receipt.json','gamma1-hecke-comparison-route-592.json'),
(594,'source-gamma-one-hecke-cosets-5-scratch-receipt.json','gamma1-hecke-square-route-594.json'),
(595,'source-gamma-one-hecke-pullback-3-scratch-receipt.json','gamma1-cohomology-hecke-compatibility-route-595.json'),
(596,'source-h1-trace-base-change-3-scratch-receipt.json','gamma1-transfer-base-change-route-596.json'),
(597,'source-gamma-one-cover-trace-base-change-4-scratch-receipt.json','gamma1-hecke-transfer-group-hypotheses-route-597.json'),
(598,'source-h1-trace-tower-4-scratch-receipt.json','gamma1-transfer-trace-composition-route-598.json')]
certs=[json.loads((p/n).read_text()) for _,n,_ in spec]
digests={n:sha(p/n) for _,n,_ in spec}
assert all(c['exit']==c['diagnostics']==0 for c in certs)
mods=sum(len(c['modules']) for c in certs)
queries=sum(len(c['queries']) for c in certs)
ths=sum(len(c['theoremRegistrations']) for c in certs)
defs=sum(len(c['constructionRegistrations']) for c in certs)
checks=sum(c['exhaustiveTheorems'] for c in certs)
edges=sum(c['requiredProofValueEdges'] for c in certs)
assert (mods,queries,ths,defs,edges)==(26,77,55,22,123)
routefile='gamma-one-hecke-trace-promotion-route-599.json'
archive='Tools/gamma-one-hecke-trace-20261025-599'
dependency='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero Galois association -> geometric Gamma1 realization -> original surjective-transfer Hecke compatibility -> exact native trace, correspondence square, group base change and trace composition'
discharged='The actual finite-index Gamma1 H1 transfer is identified with the literal native finite-coset trace, using the native counit formula and the original Shapiro cocycle comparison. Its surjectivity therefore holds for that literal trace. The actual Gamma1 constant-coefficient Hecke correspondence is defined by the original integral diagonal conjugation and full finite coset sum. Coprime principal-level reduction supplies the exact Gamma1/raised-level coset bijection, the literal cover commutes with Hecke conjugation, and the corresponding representatives have the exact conjugated transitions. Restriction of the original binary H1 to the genuine constant-coefficient Gamma1 H1 commutes with the original Hecke operator, retaining the homogeneous matrix coefficient action. Native H1 trace base change is derived by pulling back actual coinduced functions, reindexing the complete coefficient trace and applying the original Shapiro restriction/evaluation theorem. The concrete Gamma1 image has proved congruences and principal-level containment; these prove good-prime conjugation preservation, identify the exact intersection subgroup, and discharge coset surjectivity in the actual Hecke base-change application. Finally, actual nested coinduced functions form a proved isomorphism. Native quotient-product reindexing proves coefficient-trace composition, and the existing Shapiro comparison and coefficient naturality descend it to the full literal H1 trace. No trace formula, coset-surjectivity, Shapiro-composition, trace-transitivity or restriction/Hecke compatibility premise remains in these consumers.'
boundary='The surjective-transfer Hecke identity still requires combining the proved base-change and trace-composition identities with the original coefficient action and exact subgroup reindexings. Restriction compatibility alone does not establish this transfer identity. Arithmetic geometric and diamond compatibility, geometric Galois realization of the finite characters, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain required. No characteristic-zero character lift or deformation point is inferred from finite characters. 16/20; DUB-17--20 OPEN.'
route='Reuse the original coinduced coset trace, native counit, Shapiro restriction/evaluation and cocycle homotopy, existing level raising and Hecke conjugation, full SL2 reduction and its Chinese-remainder equivalence, chosen-representative coboundary comparison, native subgroup quotient maps and subgroupOf equivalence. Direct coefficient-function pullback and native quotient-product reindexing avoid new resolutions, a general Mackey development and new strong approximation. The duplicate abstract transfer-formula module remains deferred. The renewed external search and its characteristic-zero Gamma1 character boundary remain unchanged; no new external import or pin change.'
status=f'The actual Gamma1 Hecke and native trace comparison chain passes {checks} exhaustive scratch checks and 77 explicit axiom queries across 26 modules, with sixteen linters per module and zero diagnostics. Six declaration-value audits verify 123 required dependencies. Production aggregate, focused audit and sequential foundation/paper verification of the 8,274-module scope are pending.'
def output(name,s):
 f=p/name;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output(routefile,json.dumps(dict(scope=599,scopeIds=[i for i,_,_ in spec],receipts=digests,dependency=dependency,discharged=discharged,remaining=boundary,route=route,precedingCanonicalScope=8248,rootPinsChanged=False,proofLimitsChanged=False,externalImport=False,fullGoal='16/20; DUB-17--20 OPEN; all 20 acceptance gates unchanged.',reason='Combine the audited dependency chain while the preceding assembled verification finishes; do not mutate production before its canonical PASS and archive.'),indent=2)+'\n')
replacements={
'primitive-finite-gamma-one-h1-promotion-route-593.json':routefile,
'Tools/primitive-finite-gamma-one-h1-20261025-593':archive,
'Tools/primitive-witt-20261025-581':'Tools/primitive-finite-gamma-one-h1-20261025-593',
'appliedSourcePrimitiveFiniteH1Realization':'appliedSourceGammaOneHeckeTrace',
'appliedSourcePrimitiveWittDeformation':'appliedSourcePrimitiveFiniteH1Realization',
'SourcePrimitiveFiniteH1Realization':'SourceGammaOneHeckeTrace',
'primitive_finite_h1_realization':'gamma_one_hecke_trace',
'source-primitive-finite-h1-realization':'source-gamma-one-hecke-trace',
'primitive_finite_h1_canonical':'gamma_one_hecke_trace_canonical',
'SOURCE PRIMITIVE FINITE H1 REALIZATION':'SOURCE GAMMA ONE HECKE TRACE',
'actual original finite H1 characters and congruence realizations':'actual Gamma1 Hecke and native trace comparisons',
'Actual original finite H1 characters and congruence realizations':'Actual Gamma1 Hecke and native trace comparisons',
'8,248':'8,274','8,213':'8,248','8248':'8274','8213':'8248'}
rx=re.compile('|'.join(map(re.escape,sorted(replacements,key=len,reverse=True))))
transform=lambda s:rx.sub(lambda m:replacements[m[0]],s)
s=transform((p/'integrate_source_primitive_finite_h1_realization_8248.py').read_text(encoding='utf-8'))
s=re.sub(r'^digests = .+$',lambda _:'digests = '+repr(digests),s,flags=re.M)
s=s.replace('(35, 35, 96, 68, 28)','(26, 26, 77, 55, 22)')
s=s.replace('count == 205','count == '+str(checks)).replace('"increment": 35, "queries": 96','"increment": 26, "queries": 77')
for k,v in [('dependency',dependency),('discharged',discharged),('boundary',boundary),('route',route),('status',status)]:
 s=re.sub(r'^'+k+r' = .+$',lambda _,k=k,v=v:k+' = '+repr(v),s,flags=re.M)
a=s.index('evidence=[p/');b=s.index('for cert in certs:\n    evidence.append',a)
evidence=[n for _,n,_ in spec]+[n for _,_,n in spec]
for c in certs:
 evidence += [Path(c['log']).with_suffix(suffix).name for suffix in ['.lean','.log','.exit']]
 evidence += [Path(c['dependencyAuditLog']).with_suffix(suffix).name for suffix in ['.lean','.log','.exit']]
for i,_,_ in spec:
 evidence += [f.name for f in p.iterdir() if f.is_file() and f.suffix in ['.py','.json'] and re.search(r'(?<!\d)'+str(i)+r'[a-z]?\.',f.name)]
for _,name,_ in spec:
 cfg=name.replace('-scratch-receipt.json','-audit-config.json')
 assert (p/cfg).exists();evidence.append(cfg)
s=s[:a]+'evidence=[p/'+repr(routefile)+']\nevidence += [p/name for name in '+repr(sorted(set(evidence)))+']\nfor folder in [\'shapiro-h1-trace-592-before-explicit-map\',\'shapiro-h1-trace-592-before-direct-congruence\']:\n    evidence += sorted((p/folder).iterdir())\n'+s[b:]
a=s.index("    if source.is_relative_to(p/'gamma1-geometric-reuse-589'):");b=s.index('    assert not target.exists(),target',a)
s=s[:a]+"    target=r/archive_rel/(source.parent.name if source.parent != p else '')/(source.name+('.txt' if source.suffix=='.lean' else ''))\n"+s[b:]
s=s.replace("reuse['additionalCurrentSearch']","reuse['dependencyRouteAssessment']")
s=s.replace("reuse['renewedSourceArchive']","reuse['proofEvidenceArchive']")
s=re.sub(r"^    \"promotionChanges\": .+$",lambda _:'    "promotionChanges": '+repr('Only scratch imports are qualified. Every mathematical statement, proof body and module comment is preserved. The original Gamma1 cover, Hecke correspondences, binary coefficients, native cohomology, literal finite traces and subgroup reindexings retain their definitions. No source contract is weakened.')+',',s,flags=re.M)
oldedge='  PRIMITIVEFINITEH18248["Compatible original finite H1 and permutation Hecke characters with a canonical surjection, congruence-stabilizer comparison and exact constant-coefficient Gamma1 realization proved; geometric Galois realization, adic association, local/image/regularity and automorphy OPEN (DUB-17/18)"] --> CMARITH4538'
newedge='  PRIMITIVEFINITEH18248["Compatible original finite H1 and permutation Hecke characters with a canonical surjection and exact constant-coefficient Gamma1 realization (DUB-17/18)"] --> GAMMAONEHECKETRACE8274\n  GAMMAONEHECKETRACE8274["Literal native Gamma1 trace, Hecke restriction, actual Hecke base change and trace composition proved; surjective-transfer assembly, arithmetic Galois realization and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
s=re.sub(r'^edge = .+$',lambda _:'edge = '+repr(oldedge),s,flags=re.M)
s=re.sub(r'^arch.write_text\(.*$',lambda _:"arch.write_text(arch.read_text(encoding='utf-8').replace(edge,"+repr(newedge)+"),encoding='utf-8')",s,flags=re.M)
a=s.index("    '  logInfo m!");b=s.index("', b)",a)
s=s[:a]+"    '  logInfo m!\"SOURCE GAMMA ONE HECKE TRACE AUDIT PASS: {count} theorems including private/generated declarations. The literal native Gamma1 trace, original Hecke restriction compatibility, actual Hecke base change and trace composition are proved. Surjective-transfer assembly, arithmetic Galois realization, all-weight association and higher continuation remain open; 16/20 gates.\"\\n"+s[b:]
output('integrate_source_gamma_one_hecke_trace_8274.py',s)
for stem in ['prepare_primitive_finite_h1_realization_production_ownership','prepare_primitive_finite_h1_realization_scratch_ownership','compare_primitive_finite_h1_realization_ownership','prepare_primitive_finite_h1_realization_global_ownership']:
 s=transform((p/(stem+'_8248.py')).read_text(encoding='utf-8'))
 s=re.sub(r'\b205\b',str(checks),s)
 s=s.replace('len(names)==len(certs)==7','len(names)==len(certs)==6').replace('All 35 mathematical','All 26 mathematical')
 output(transform(stem+'_8248.py'),s)
s=transform((p/'record_source_primitive_finite_h1_realization_8248b.py').read_text(encoding='utf-8'))
s=re.sub(r'\b205\b',str(checks),s)
s=s.replace('== 35','== 26').replace('"incrementModules": 35','"incrementModules": 26').replace('"linterScopes": 35','"linterScopes": 26')
s=s.replace('len(ownershipComparison["scopes"]) == 7','len(ownershipComparison["scopes"]) == 6')
s=s.replace('Seven declaration-value audits verify 157 required dependencies.','Six declaration-value audits verify 123 required dependencies.')
s=s.replace('int(a[2]) == 23789','int(a[2]) == 23844')
output('record_source_gamma_one_hecke_trace_8274.py',s)
for stem in ['build_primitive_finite_h1_realization','verify_primitive_finite_h1_realization']:
 output(transform(stem+'_8248.ps1'),transform((p/(stem+'_8248.ps1')).read_text(encoding='utf-8')))
output('archive_gamma_one_hecke_trace_canonical_8274.py',transform((p/'archive_primitive_finite_h1_canonical_8248.py').read_text(encoding='utf-8')))
scripts=[f for f in p.iterdir() if re.search(r'8274\.(py|ps1)$',f.name) and f.name!='prepare_gamma_one_hecke_trace_promotion_8274.py']
for f in scripts:
 t=f.read_text(encoding='utf-8')
 if f.suffix=='.py':ast.parse(t)
 assert '16/22' not in t and 'DUB-17-22' not in t,f
review=dict(status='Prepared; require 8248 canonical PASS and immutable archive before integration.',route=routefile,routeSha256=sha(p/routefile),modules=mods,queries=queries,theorems=ths,constructions=defs,exhaustiveScratchChecks=checks,proofValueEdges=edges,scopes=6,receipts=digests,sourceScopes=[i for i,_,_ in spec],expectedConsumers=23844,expectedConstructions=2277,fullGoal='16/20; DUB-17--20 OPEN; all 20 gates unchanged.',sourceBodies='Audited statements, bodies and comments unchanged; only scratch project imports qualified.',scripts=[dict(path=str(f),sha256=sha(f)) for f in scripts],productionMutation=False)
output('gamma-one-hecke-trace-preexecution-review-8274.json',json.dumps(review,indent=2)+'\n')
print(json.dumps(dict(scripts=len(scripts),modules=mods,queries=queries,exhaustive=checks,edges=edges,productionMutation=False)))
