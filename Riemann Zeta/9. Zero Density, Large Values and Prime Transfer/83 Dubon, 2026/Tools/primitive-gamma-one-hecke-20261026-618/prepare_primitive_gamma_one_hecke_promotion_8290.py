from pathlib import Path
import ast,json,re,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
spec=[
(600,'source-gamma-one-binary-trace-2-scratch-receipt.json','gamma1-binary-hecke-transfer-reduction-route-600.json'),
(601,'source-gamma-one-hecke-upper-image-1-scratch-receipt.json','gamma1-hecke-trace-subgroup-reindex-route-601.json'),
(602,'source-gamma-one-subgroup-h1-map-1-scratch-receipt.json','gamma1-subgroup-h1-transfer-identification-route-602.json'),
(605,'source-gamma-one-native-hecke-comparison-2-scratch-receipt.json','gamma1-native-hecke-comparison-route-605.json'),
(611,'source-gamma-one-transfer-hecke-5-scratch-receipt.json','gamma1-actual-transfer-hecke-route-611.json'),
(617,'source-primitive-gamma-one-character-5b-scratch-receipt.json','gamma1-original-finite-character-route-617b.json')]
certs=[json.loads((p/n).read_text()) for _,n,_ in spec]
digests={n:sha(p/n) for _,n,_ in spec}
assert all(c['exit']==c['diagnostics']==0 for c in certs)
mods=sum(len(c['modules']) for c in certs)
queries=sum(len(c['queries']) for c in certs)
ths=sum(len(c['theoremRegistrations']) for c in certs)
defs=sum(len(c['constructionRegistrations']) for c in certs)
checks=sum(c['exhaustiveTheorems'] for c in certs)
edges=sum(c['requiredProofValueEdges'] for c in certs)
assert (mods,queries,ths,defs,edges)==(16,41,30,11,78)
routefile='primitive-gamma-one-hecke-promotion-route-618.json'
archive='Tools/primitive-gamma-one-hecke-20261026-618'
dependency='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero Galois association -> arithmetic Gamma1 geometric realization -> actual surjective-transfer Hecke compatibility and original finite Fourier-valued Gamma1 characters'
discharged='The already constructed surjective constant-coefficient Gamma1 H1 transfer now intertwines the actual full original binary Hecke operators at every prime coprime to level times coefficient modulus, retaining the homogeneous matrix coefficient action. Native trace base change with the original coefficient morphism, the exact upper-subgroup isomorphism, the native H1 pullback square and upper-trace reindexing are proved. Applying the existing trace tower through the same actual intersection proves trace exchange; composing these identities and the original literal-transfer formula discharges the full surjective-transfer compatibility. The same actual transfer and existing additive word intertwiner then force every Gamma1 operator relation to hold in the original finite tensor-operator image. Native ring-map descent constructs its canonical comparison. For every original primitive form of weight at least two and every prescribed prime greater than three, the original local embedding and compatible adic character supply characters on the actual finite Gamma1 H1 operator rings at all positive prime-power precisions. Whole-word pullback and the exact original Fourier values at primes away from level and modulus are derived. Native congruence-group finite generation and the existing finite H1 theorem prove these actual operator rings finite. No trace, subgroup, coefficient-action, operator-relation or character-existence premise remains in these consumers.'
boundary='Arithmetic geometric and diamond compatibility, geometric Galois realization of the finite characters, original all-weight characteristic-zero association, required local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain required. The new operator generators explicitly omit primes dividing level or modulus; surjectivity onto the entire original Hecke algebra is not asserted. No characteristic-zero character lift or deformation point is inferred from finite characters. 16/20; DUB-17--20 OPEN.'
route='Reuse the existing native trace tower, cohomology reindexing, coefficient trace naturality, exact congruence subgroup identities and literal original transfer. Apply the proved additive word intertwiner, exact integral reduction kernel, finite operator-character descent, original Fourier character and prescribed-prime completion. Existing finite group-cohomology and the homogeneous monomial basis prove finiteness. Small native map projections and explicit ring objects avoid elaboration timeouts at unchanged limits. The exhaustive linter removed an unnecessary nonzero-modulus binder from the operator definitions; all failed evidence is preserved. No general Mackey development, new word induction, arbitrary eigenvector lift or substitute Hecke operator is used. The renewed external search and its characteristic-zero Gamma1 character boundary remain unchanged; no new external import or pin change.'
status=f'The actual Gamma1 transfer and original-form finite-character chain passes {checks} exhaustive scratch checks and 41 explicit axiom queries across 16 modules, with sixteen linters per module and zero diagnostics. Six declaration-value audits verify 78 required dependencies. Production aggregate, focused audit and sequential foundation/paper verification of the 8,290-module scope are pending.'
def output(name,s):
 f=p/name;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output(routefile,json.dumps(dict(scope=618,scopeIds=[i for i,_,_ in spec],receipts=digests,dependency=dependency,discharged=discharged,remaining=boundary,route=route,precedingCanonicalScope=8274,rootPinsChanged=False,proofLimitsChanged=False,externalImport=False,fullGoal='16/20; DUB-17--20 OPEN; all 20 acceptance gates unchanged.',reason='Prepare the audited dependency chain while the preceding assembled verification finishes. Require canonical PASS and immutable archive before production mutation.'),indent=2)+'\n')
replacements={
'gamma-one-hecke-trace-promotion-route-599.json':routefile,
'Tools/gamma-one-hecke-trace-20261025-599':archive,
'Tools/primitive-finite-gamma-one-h1-20261025-593':'Tools/gamma-one-hecke-trace-20261025-599',
'appliedSourceGammaOneHeckeTrace':'appliedSourcePrimitiveGammaOneHeckeRealization',
'appliedSourcePrimitiveFiniteH1Realization':'appliedSourceGammaOneHeckeTrace',
'SourceGammaOneHeckeTrace':'SourcePrimitiveGammaOneHeckeRealization',
'gamma_one_hecke_trace':'primitive_gamma_one_hecke_realization',
'source-gamma-one-hecke-trace':'source-primitive-gamma-one-hecke-realization',
'SOURCE GAMMA ONE HECKE TRACE':'SOURCE PRIMITIVE GAMMA ONE HECKE REALIZATION',
'actual Gamma1 Hecke and native trace comparisons':'actual Gamma1 transfer and original-form finite characters',
'Actual Gamma1 Hecke and native trace comparisons':'Actual Gamma1 transfer and original-form finite characters',
'8,274':'8,290','8,248':'8,274','8274':'8290','8248':'8274'}
rx=re.compile('|'.join(map(re.escape,sorted(replacements,key=len,reverse=True))))
transform=lambda s:rx.sub(lambda m:replacements[m[0]],s)
s=transform((p/'integrate_source_gamma_one_hecke_trace_8274.py').read_text(encoding='utf-8'))
s=re.sub(r'^digests = .+$',lambda _:'digests = '+repr(digests),s,flags=re.M)
s=s.replace('(26, 26, 77, 55, 22)','(16, 16, 41, 30, 11)').replace('count == 111','count == '+str(checks)).replace('"increment": 26, "queries": 77','"increment": 16, "queries": 41')
s=s.replace('key = "appliedSourcePrimitiveGammaOneHeckeRealization"',"assert (r/'Tools/gamma-one-hecke-trace-20261025-599/canonical-evidence-8274.json').exists()\nkey = \"appliedSourcePrimitiveGammaOneHeckeRealization\"")
for k,v in [('dependency',dependency),('discharged',discharged),('boundary',boundary),('route',route),('status',status)]:
 s=re.sub(r'^'+k+r' = .+$',lambda _,k=k,v=v:k+' = '+repr(v),s,flags=re.M)
a=s.index('evidence=[p/');b=s.index('for cert in certs:\n    evidence.append',a)
evidence=[n for _,n,_ in spec]+[n for _,_,n in spec]
for c in certs:
 for field in ['log','dependencyAuditLog']:
  evidence += [Path(c[field]).with_suffix(suffix).name for suffix in ['.lean','.log','.exit']]
for i in [600,601,602,603,604,605,606,611,612,613,617]:
 evidence += [f.name for f in p.iterdir() if f.is_file() and f.suffix in ['.py','.json','.txt'] and re.search(r'(?<!\d)'+str(i)+r'[a-z]?(?:\.|-)',f.name)]
for _,name,_ in spec:
 cfg=name.replace('-scratch-receipt.json','-audit-config.json')
 assert (p/cfg).exists();evidence.append(cfg)
for name in ['SourcePrimitiveGammaOneCharacterAudit5.lean','SourcePrimitiveGammaOneCharacterAudit5.log','SourcePrimitiveGammaOneCharacterAudit5.exit','SourcePrimitiveGammaOneCharacterDependencyAudit5.lean','source-primitive-gamma-one-character-5-audit-config.json']:
 assert (p/name).exists();evidence.append(name)
folders=[f.name for f in p.iterdir() if f.is_dir() and (re.match(r'(?:h1-trace-coefficient-600|gamma1-subgroup-h1-602|gamma1-hecke-pullback-603|gamma1-operator-descent-613|gamma1-character-617)-before-',f.name))]
assert len(folders)>=10,folders
s=s[:a]+'evidence=[p/'+repr(routefile)+']\nevidence += [p/name for name in '+repr(sorted(set(evidence)))+']\nfor folder in '+repr(folders)+':\n    evidence += sorted((p/folder).iterdir())\n'+s[b:]
oldedge='  GAMMAONEHECKETRACE8274["Literal native Gamma1 trace, Hecke restriction, actual Hecke base change and trace composition proved; surjective-transfer assembly, arithmetic Galois realization and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
newedge='  GAMMAONEHECKETRACE8274["Literal native Gamma1 trace, Hecke restriction, actual Hecke base change and trace composition (DUB-17/18)"] --> PRIMITIVEGAMMAONE8290\n  PRIMITIVEGAMMAONE8290["Actual surjective Gamma1 transfer/Hecke compatibility and original Fourier-valued finite Gamma1 operator characters proved; arithmetic geometric and diamond comparison, Galois realization and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
s=re.sub(r'^edge = .+$',lambda _:'edge = '+repr(oldedge),s,flags=re.M)
s=re.sub(r'^arch.write_text\(.*$',lambda _:"arch.write_text(arch.read_text(encoding='utf-8').replace(edge,"+repr(newedge)+"),encoding='utf-8')",s,flags=re.M)
a=s.index("    '  logInfo m!");b=s.index("', b)",a)
s=s[:a]+'    \'  logInfo m!"SOURCE PRIMITIVE GAMMA ONE HECKE REALIZATION AUDIT PASS: {count} theorems including private/generated declarations. The actual surjective Gamma1 transfer intertwines full Hecke operators, and every original primitive form supplies finite Gamma1 operator characters with original Fourier values. Arithmetic geometric and diamond comparison, Galois realization, all-weight association and higher continuation remain open; 16/20 gates."\\n'+s[b:]
output('integrate_source_primitive_gamma_one_hecke_realization_8290.py',s)
for stem in ['prepare_gamma_one_hecke_trace_production_ownership','prepare_gamma_one_hecke_trace_scratch_ownership','compare_gamma_one_hecke_trace_ownership','prepare_gamma_one_hecke_trace_global_ownership']:
 s=transform((p/(stem+'_8274.py')).read_text(encoding='utf-8'))
 s=re.sub(r'\b111\b',str(checks),s).replace('All 26 mathematical','All 16 mathematical')
 output(transform(stem+'_8274.py'),s)
s=transform((p/'record_source_gamma_one_hecke_trace_8274.py').read_text(encoding='utf-8'))
s=re.sub(r'\b111\b',str(checks),s)
s=s.replace('== 26','== 16').replace('"incrementModules": 26','"incrementModules": 16').replace('"linterScopes": 26','"linterScopes": 16').replace('Six declaration-value audits verify 123 required dependencies.','Six declaration-value audits verify 78 required dependencies.').replace('int(a[2]) == 23844','int(a[2]) == 23874')
output('record_source_primitive_gamma_one_hecke_realization_8290.py',s)
for stem in ['build_gamma_one_hecke_trace','verify_gamma_one_hecke_trace']:
 s=transform((p/(stem+'_8274.ps1')).read_text(encoding='utf-8')).replace('# Scratch ownership was independently executed before promotion; preserve its logs.','# Preserve independently executed scratch ownership logs; do not rerun them.')
 output(transform(stem+'_8274.ps1'),s)
output('archive_primitive_gamma_one_hecke_realization_canonical_8290.py',transform((p/'archive_gamma_one_hecke_trace_canonical_8274.py').read_text(encoding='utf-8')))
scripts=[f for f in p.iterdir() if re.search(r'8290\.(py|ps1)$',f.name) and f.name!='prepare_primitive_gamma_one_hecke_promotion_8290.py']
for f in scripts:
 t=f.read_text(encoding='utf-8')
 if f.suffix=='.py':ast.parse(t)
 assert '16/22' not in t and 'DUB-17-22' not in t,f
review=dict(status='Prepared; require 8274 canonical PASS and immutable archive before integration.',route=routefile,routeSha256=sha(p/routefile),modules=mods,queries=queries,theorems=ths,constructions=defs,exhaustiveScratchChecks=checks,proofValueEdges=edges,scopes=6,receipts=digests,sourceScopes=[i for i,_,_ in spec],expectedConsumers=23874,expectedConstructions=2288,fullGoal='16/20; DUB-17--20 OPEN; all 20 gates unchanged.',sourceBodies='Audited statements, bodies and comments unchanged; only scratch project imports qualified.',scripts=[dict(path=str(f),sha256=sha(f)) for f in scripts],productionMutation=False)
output('primitive-gamma-one-hecke-preexecution-review-8290.json',json.dumps(review,indent=2)+'\n')
print(json.dumps(dict(scripts=len(scripts),modules=mods,queries=queries,exhaustive=checks,edges=edges,productionMutation=False)))
