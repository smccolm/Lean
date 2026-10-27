from pathlib import Path
import ast,json,re,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
names=['source-fricke-cyclotomic-transport-3-scratch-receipt.json','source-fricke-product-transport-4-scratch-receipt.json','source-fricke-separation-5-scratch-receipt.json','source-level-one-analytic-polynomial-3-scratch-receipt.json','source-fricke-level-field-7d-scratch-receipt.json','source-fricke-stable-family-5c-scratch-receipt.json','source-fricke-orbit-monic-2b-scratch-receipt.json','source-fricke-j-transcendence-1-scratch-receipt.json']
certs=[json.loads((p/n).read_text(encoding='utf-8')) for n in names]
digests={n:sha(p/n) for n in names}
assert tuple(sum(len(c[k]) for c in certs) for k in ['modules','queries','theoremRegistrations','constructionRegistrations'])==(30,192,140,52)
assert sum(c['exhaustiveTheorems'] for c in certs)==262
assert sum(c['requiredProofValueEdges'] for c in certs)==224
routefile='fricke-rational-structure-inputs-promotion-route-664.json'
archive='Tools/fricke-rational-structure-inputs-20261026-664'
dependency='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> arithmetic realization of original finite Gamma1 Hecke characters -> actual Picard/H1, full/parabolic and diamond comparison retaining the original homogeneous coefficient endomorphism -> actual regular differential/cusp comparison -> cyclotomic rational Fourier spanning -> Fricke fractions and integral relations.'
discharged='Actual torsion Fourier coefficients and the actual Fricke numerator transport under cyclotomic embeddings. The proved period map separates actual torsion Weierstrass values up to sign, giving the exact Fricke action kernel. The existing level-one Laurent polynomial identity transfers to actual analytic forms: weight 12m forms are Delta^m times a polynomial in actual j of degree at most m. The fixed subfield of the actual Fricke fraction field is exactly C(j), with degree the exact stabilizer index. A holomorphic principal-level invariant function with finite cusp poles at every modular translate is an actual Fricke fraction and satisfies an actual monic equation over C[j]; its modular orbit, the surjectivity of the fraction-field inclusion and the monic relation are derived. Existing actual j surjectivity proves its transcendence in the actual Fricke field. No fraction representation, fixed-field equality, monic relation, separation or transcendence premise is supplied.'
boundary='Cyclotomic integral base change, rational Fourier spanning and the actual algebraic realization of arbitrary Gamma1 cusp forms remain; the converse regular-differential-to-cusp construction also remains. The actual Picard/H1, full/parabolic, transpose and diamond comparison must identify the original finite homogeneous-coefficient Hecke characters with geometric characters. Frobenius/inertia, arithmetic realization of these characters, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain required. Neither complex semisimplicity, finite characters, Witt coefficients nor a universal deformation ring supplies a characteristic-zero lift or point. 16/20; DUB-17--20 OPEN.'
route='The renewed search is recorded in Dubon Reuse Search 2026-10-26.md. Fixed-revision primary snapshots and selected-file assessments are archived here. Reuse the actual elliptic period map for separation, the existing sparse Fourier reindexing and native Eisenstein coefficients for rational prefactors, the proved level-one Laurent polynomial identity for invariant analytic functions, native finite-action characteristic polynomials for the monic relation, and actual j surjectivity for transcendence. Native fixed-field degree and a finite orbit denominator prove stable-family fraction realization. Existing Laurent coefficient retraction and scalar independence are candidates for the next descent step; their Fourier-realization bridges remain unproved. The new external integral-span and constant-extension sources are research only, with no full external import-closure verification claim. Earlier source/object evidence affected by variable cleanup is not used for promotion; the final V3/V2 sources have fresh sequential builds and audits. Failed API, typeclass, linter and named-dependency evidence is retained. Native scalar aliases absent from terminal values retain explicit axiom checks without a named-use claim. No audited source or used audit is rewritten. No external project was built or imported; pins, proof limits and all twenty acceptance gates are unchanged.'
status='The actual Fricke rational-structure inputs pass 262 exhaustive scratch theorem checks and 192 public axiom queries across 30 modules, with sixteen linters per module and zero diagnostics. Eight declaration-value audits verify 224 required dependencies. Production aggregate, focused audit and sequential foundation/paper verification of the 8,390-module scope are pending.'
def output(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output(routefile,json.dumps(dict(scope=664,scopeIds=['652','654','655','657','658d','659c','660b','663'],receipts=digests,dependency=dependency,discharged=discharged,remaining=boundary,route=route,precedingCanonicalScope=8360,rootPinsChanged=False,proofLimitsChanged=False,externalImport=False,fullGoal='16/20; DUB-17--20 OPEN; all 20 acceptance gates unchanged.',reason='Require preceding canonical PASS and immutable archive before production mutation.'),indent=2)+'\n')
repl={
'gamma-one-regularity-fricke-inputs-promotion-route-653.json':routefile,
'Tools/gamma-one-regularity-fricke-inputs-20261026-653':archive,
'Tools/gamma-one-differential-inputs-20261026-641':'Tools/gamma-one-regularity-fricke-inputs-20261026-653',
'appliedSourceGammaOneRegularityFrickeInputs':'appliedSourceFrickeRationalStructureInputs',
'appliedSourceGammaOneDifferentialInputs':'appliedSourceGammaOneRegularityFrickeInputs',
'SourceGammaOneRegularityFrickeInputs':'SourceFrickeRationalStructureInputs',
'gamma_one_regularity_fricke_inputs':'fricke_rational_structure_inputs',
'source-gamma-one-regularity-fricke-inputs':'source-fricke-rational-structure-inputs',
'SOURCE GAMMA ONE REGULARITY FRICKE INPUTS':'SOURCE FRICKE RATIONAL STRUCTURE INPUTS',
'actual Gamma1 regularity and Fricke Fourier inputs':'actual Fricke rational-structure inputs',
'Actual Gamma1 regularity and Fricke Fourier inputs':'Actual Fricke rational-structure inputs',
'8,360':'8,390','8,335':'8,360','8360':'8390','8335':'8360'}
rx=re.compile('|'.join(map(re.escape,sorted(repl,key=len,reverse=True))))
tr=lambda s:rx.sub(lambda m:repl[m[0]],s)
s=tr((p/'integrate_source_gamma_one_regularity_fricke_inputs_8360.py').read_text(encoding='utf-8'))
s=re.sub(r'^digests = .+$',lambda _:'digests = '+repr(digests),s,flags=re.M)
s=s.replace('(25, 25, 152, 126, 26)','(30, 30, 192, 140, 52)').replace('count == 264','count == 262').replace('"increment": 25, "queries": 152','"increment": 30, "queries": 192')
for k,v in [('dependency',dependency),('discharged',discharged),('boundary',boundary),('route',route),('status',status)]:
 s=re.sub(r'^'+k+r' = .+$',lambda _,k=k,v=v:k+' = '+repr(v),s,flags=re.M)
a=s.index('evidence=[p/');b=s.index("for cert in certs:\n    evidence.append",a)
evidence=list(digests)
for cert in certs:
 for key in ['log','dependencyAuditLog']:
  f=Path(cert[key]);evidence += [f.with_suffix(ext).name for ext in ['.lean','.log','.exit']]
 review=json.loads(Path(cert['reuseReview']).read_text(encoding='utf-8'))
 evidence.append(Path(review['routeAssessment']['path']).name)
for f in p.iterdir():
 if f.is_file() and f.suffix in ['.json','.py','.txt'] and re.search(r'(?<!\d)(652|654|655|656|657|658|659|660|661|662|663)[a-z]?(?:\.|-)',f.name):evidence.append(f.name)
for certName in names:evidence.append(certName.replace('-scratch-receipt.json','-audit-config.json'))
for pat in ['SourceFrickeLevelFieldAudit7*','SourceFrickeLevelFieldDependencyAudit7*','SourceFrickeStableFamilyAudit5*','SourceFrickeStableFamilyDependencyAudit5*','SourceFrickeOrbitMonicAudit2*','SourceFrickeOrbitMonicDependencyAudit2*']:
 evidence += [f.name for f in p.glob(pat) if f.suffix in ['.lean','.log','.exit']]
oldmods=['SourceFrickePoleBounded','SourceFrickeHolomorphicAlgebra','SourceFrickeLevelAlgebra','SourceFrickeLevelGroup','SourceFrickeLevelField','SourceFrickeFixedFraction','SourceFrickeFixedFieldJ']
oldmods += [m+'V2' for m in oldmods]
oldmods += ['SourceFrickeStableAlgebra','SourceFrickeStableGroup','SourceFrickeStableField','SourceFrickeStableEmbedding','SourceFrickeStableFraction','SourceFrickeStableMonic','SourceFrickeModularOrbit']
for m in oldmods:evidence += [f.name for ext in ['.lean','.log','.exit'] if (f:=p/(m+ext)).exists()]
folders=['fricke-level-structure-reuse-656','fricke-rational-descent-reuse-661','fricke-base-change-dependencies-reuse-662','fricke-level-field-api-failure-658','fricke-level-field-instance-failure-658','fricke-fixed-field-j-instance-failure-658','fricke-fixed-field-j-action-failure-658','fricke-stable-field-instance-failure-659','fricke-stable-v2-before-variable-cleanup-659b']
evidence=sorted(set(evidence))
for n in evidence+folders:assert (p/n).exists(),n
s=s[:a]+'evidence=[p/'+repr(routefile)+']\nevidence += [p/n for n in '+repr(evidence)+']\nfor folder in '+repr(folders)+':\n    evidence += sorted(f for f in (p/folder).rglob("*") if f.is_file())\n'+s[b:]
oldedge='  GAMMAONEREG8360["Actual Gamma1 cusp-matching differentials are regular; original Fricke transformation, holomorphy, torsion cyclotomic Fourier coefficients and cusp bounds proved. Rational spanning, realization, converse, Picard/H1/diamond, arithmetic realization and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
newedge='  GAMMAONEREG8360["Actual Gamma1 cusp-matching regularity and original Fricke Fourier inputs (DUB-17/18)"] --> FRICKERAT8390\n  FRICKERAT8390["Actual cyclotomic transport, Fricke separation, fixed field C(j), stable-family fraction realization and monic relations proved. Rational spanning, differential realization, converse, Picard/H1/diamond, original arithmetic realization and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
s=re.sub(r'^edge = .+$',lambda _:'edge = '+repr(oldedge),s,flags=re.M)
s=re.sub(r'^arch.write_text\(.*$',lambda _:"arch.write_text(arch.read_text(encoding='utf-8').replace(edge,"+repr(newedge)+"),encoding='utf-8')",s,flags=re.M)
s=re.sub(r'^    "promotionChanges": .+$',lambda _:'    "promotionChanges": '+repr('Only scratch imports are qualified. Every final audited statement, proof body and comment is preserved. All functions, torsion indices, coefficient fields, algebras, actions and embeddings are the actual constructed objects. No source contract is weakened.')+',',s,flags=re.M)
logline='  logInfo m!"SOURCE FRICKE RATIONAL STRUCTURE INPUTS AUDIT PASS: {count} theorems including private/generated declarations. Actual cyclotomic transport, Fricke separation, fixed field, stable-family fractions, monic relations and j transcendence are proved. Rational spanning, differential realization and arithmetic comparison remain; 16/20 gates."\n'
a=s.index("b = re.sub('  logInfo");b=s.index(', b)',a)+len(', b)')
s=s[:a]+'b = re.sub('+repr('  logInfo m!".*"\n')+', '+repr(logline)+', b)'+s[b:]
output('integrate_source_fricke_rational_structure_inputs_8390.py',s)
scripts=['integrate_source_fricke_rational_structure_inputs_8390.py']
for stem in ['prepare_gamma_one_regularity_fricke_inputs_production_ownership','prepare_gamma_one_regularity_fricke_inputs_scratch_ownership','compare_gamma_one_regularity_fricke_inputs_ownership','prepare_gamma_one_regularity_fricke_inputs_global_ownership']:
 s=tr((p/(stem+'_8360.py')).read_text(encoding='utf-8'))
 s=re.sub(r'\b264\b','262',s).replace('All 25 mathematical','All 30 mathematical').replace('len(names)==len(certs)==4','len(names)==len(certs)==8')
 n=tr(stem+'_8360.py');output(n,s);scripts.append(n)
s=tr((p/'record_source_gamma_one_regularity_fricke_inputs_8360.py').read_text(encoding='utf-8'))
s=re.sub(r'\b264\b','262',s).replace('== 25','== 30').replace('"incrementModules": 25','"incrementModules": 30').replace('"linterScopes": 25','"linterScopes": 30')
s=s.replace('len(ownershipComparison["scopes"]) == 4','len(ownershipComparison["scopes"]) == 8').replace('Four declaration-value audits verify 162 required dependencies.','Eight declaration-value audits verify 224 required dependencies.').replace('int(a[2]) == 24150','int(a[2]) == 24290')
n='record_source_fricke_rational_structure_inputs_8390.py';output(n,s);scripts.append(n)
for stem in ['build_gamma_one_regularity_fricke_inputs','verify_gamma_one_regularity_fricke_inputs']:
 n=tr(stem+'_8360.ps1');output(n,tr((p/(stem+'_8360.ps1')).read_text(encoding='utf-8')));scripts.append(n)
n='archive_fricke_rational_structure_inputs_canonical_8390.py';output(n,tr((p/'archive_gamma_one_regularity_fricke_inputs_canonical_8360.py').read_text(encoding='utf-8')));scripts.append(n)
for n in scripts:
 f=p/n;t=f.read_text(encoding='utf-8')
 if f.suffix=='.py':ast.parse(t)
 assert '16/22' not in t and 'DUB-17-22' not in t,f
output('fricke-rational-structure-inputs-preexecution-review-8390.json',json.dumps(dict(status='Prepared; require 8360 canonical PASS and archive before integration.',route=routefile,routeSha256=sha(p/routefile),modules=30,queries=192,theorems=140,constructions=52,exhaustiveScratchChecks=262,proofValueEdges=224,scopes=8,receipts=digests,expectedConsumers=24290,expectedConstructions=2403,fullGoal='16/20; DUB-17--20 OPEN; all 20 gates unchanged.',scripts=[dict(path=str(p/n),sha256=sha(p/n)) for n in scripts],productionMutation=False),indent=2)+'\n')
print(json.dumps(dict(scripts=len(scripts),modules=30,productionMutation=False)))
