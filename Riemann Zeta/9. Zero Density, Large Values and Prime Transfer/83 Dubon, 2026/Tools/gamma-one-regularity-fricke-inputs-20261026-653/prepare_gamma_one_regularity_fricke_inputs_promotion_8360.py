from pathlib import Path
import ast,json,re,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
names=['source-gamma-one-differential-regularity-6b-scratch-receipt.json','source-fricke-transformation-4c-scratch-receipt.json','source-weierstrass-expansion-8b-scratch-receipt.json','source-fricke-fourier-coefficients-7b-scratch-receipt.json']
certs=[json.loads((p/n).read_text(encoding='utf-8')) for n in names]
digests={n:sha(p/n) for n in names}
assert tuple(sum(len(c[k]) for c in certs) for k in ['modules','queries','theoremRegistrations','constructionRegistrations'])==(25,152,126,26)
assert sum(c['exhaustiveTheorems'] for c in certs)==264
assert sum(c['requiredProofValueEdges'] for c in certs)==162
routefile='gamma-one-regularity-fricke-inputs-promotion-route-653.json'
archive='Tools/gamma-one-regularity-fricke-inputs-20261026-653'
dependency='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> arithmetic realization of original finite Gamma1 Hecke characters -> actual Picard/H1, full/parabolic and diamond comparison retaining the original homogeneous coefficient endomorphism -> actual regular differential/cusp comparison -> regularity and rational Fourier structure.'
discharged='For the actual Gamma1 integral-ratio Laurent field, every differential whose mapped expansion equals an actual weight-two cusp expansion is regular at every place. Both integral equations, coefficient descent, local orders and curve prerequisites are derived. The original normalized Fricke functions transform by the actual torsion-index action, are invariant under the principal subgroup and unchanged by index negation. Native Lipschitz summation and absolute Weierstrass summability prove the exact torsion Fourier formula and holomorphy. The actual normalized torsion functions are periodic, bounded at infinity and have explicit Fourier coefficients in the level cyclotomic field. Multiplication of the original Fricke function by Delta gives a bounded function at infinity. No regularity, Fourier identity, holomorphy, coefficient-field or cusp-bound premise is assumed.'
boundary='Algebraic realization of arbitrary Gamma1 cusp forms and the converse regular-differential-to-cusp construction remain. The actual Picard/H1, full/parabolic, transpose and diamond comparison must identify the original finite homogeneous-coefficient Hecke characters with geometric characters. Frobenius/inertia, arithmetic realization of these characters, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain required. Neither complex semisimplicity, finite characters, Witt coefficients nor a universal deformation ring supplies a characteristic-zero lift or point. 16/20; DUB-17--20 OPEN.'
route='The renewed search is recorded in Dubon Reuse Search 2026-10-26.md; the exact fixed-revision primary proofs and adaptation assessments are archived here. Reuse a native linear retraction for coefficient descent, the previously proved actual Gamma1 integral equations and curve prerequisites, the actual Weierstrass lattice and native modular transformations. Native weight-two Lipschitz summation, absolute lattice summability, locally uniform differentiation and finite-product summability avoid duplicate foundations. Keep the integer-complement boundary case required by torsion points with first coordinate zero. Finite exponent fibers and native Fourier uniqueness give the actual cyclotomic coefficients. The rational Hecke-matrix basis does not supply the missing Gamma1 rational Fourier basis. Failed timeout, documentation, preflight and dependency-audit evidence is preserved with fresh successors. No used audit or audited mathematical body is rewritten. No external project was built or imported; pins, proof limits and all twenty gates are unchanged.'
status='The actual Gamma1 regularity and Fricke Fourier inputs pass 264 exhaustive scratch checks and 152 public axiom queries across 25 modules, with sixteen linters per module and zero diagnostics. Four declaration-value audits verify 162 required dependencies. Production aggregate, focused audit and sequential foundation/paper verification of the 8,360-module scope are pending.'
def output(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output(routefile,json.dumps(dict(scope=653,scopeIds=['643b','647c','650b','651b'],receipts=digests,dependency=dependency,discharged=discharged,remaining=boundary,route=route,precedingCanonicalScope=8335,rootPinsChanged=False,proofLimitsChanged=False,externalImport=False,fullGoal='16/20; DUB-17--20 OPEN; all 20 acceptance gates unchanged.',reason='Require preceding canonical PASS and immutable archive before production mutation.'),indent=2)+'\n')
repl={
'gamma-one-differential-inputs-promotion-route-641.json':routefile,
'Tools/gamma-one-differential-inputs-20261026-641':archive,
'Tools/gamma-one-arithmetic-geometry-20261026-626':'Tools/gamma-one-differential-inputs-20261026-641',
'appliedSourceGammaOneDifferentialInputs':'appliedSourceGammaOneRegularityFrickeInputs',
'appliedSourceGammaOneArithmeticGeometry':'appliedSourceGammaOneDifferentialInputs',
'SourceGammaOneDifferentialInputs':'SourceGammaOneRegularityFrickeInputs',
'gamma_one_differential_inputs':'gamma_one_regularity_fricke_inputs',
'source-gamma-one-differential-inputs':'source-gamma-one-regularity-fricke-inputs',
'SOURCE GAMMA ONE DIFFERENTIAL INPUTS':'SOURCE GAMMA ONE REGULARITY FRICKE INPUTS',
'actual Gamma1 cohomology and differential inputs':'actual Gamma1 regularity and Fricke Fourier inputs',
'Actual Gamma1 cohomology and differential inputs':'Actual Gamma1 regularity and Fricke Fourier inputs',
'8,335':'8,360','8,316':'8,335','8335':'8360','8316':'8335'}
rx=re.compile('|'.join(map(re.escape,sorted(repl,key=len,reverse=True))))
tr=lambda s:rx.sub(lambda m:repl[m[0]],s)
s=tr((p/'integrate_source_gamma_one_differential_inputs_8335.py').read_text(encoding='utf-8'))
s=re.sub(r'^digests = .+$',lambda _:'digests = '+repr(digests),s,flags=re.M)
s=s.replace('(19, 19, 85, 73, 12)','(25, 25, 152, 126, 26)').replace('count == 138','count == 264').replace('"increment": 19, "queries": 85','"increment": 25, "queries": 152')
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
 if f.is_file() and f.suffix in ['.json','.py','.txt'] and re.search(r'(?<!\d)(642|643|644|646|647|648|649|650|651)[a-z]?(?:\.|-)',f.name):
  evidence.append(f.name)
for n in ['source-gamma-one-differential-regularity-6b','source-fricke-transformation-4c','source-weierstrass-expansion-8b','source-fricke-fourier-coefficients-7b']:
 evidence.append(n+'-audit-config.json')
for base in ['SourceGammaOneDifferentialRegularityDependencyAudit6','SourceFrickeTransformationAudit4','SourceFrickeTransformationDependencyAudit4b','SourceWeierstrassExpansionDependencyAudit8','SourceFrickeFourierCoefficientsAudit7','SourceFrickePeriodHomothety','SourceFrickeModularLattice','SourceFrickeTorsionTransformation','SourceFrickeFunctionTransformation']:
 evidence += [f.name for ext in ['.lean','.log','.exit'] if (f:=p/(base+ext)).exists()]
folders=['gamma1-regularity-descent-reuse-642','gamma1-cusp-realization-reuse-644','gamma1-rational-structure-input-reuse-646','fricke-torsion-expansion-reuse-648','weierstrass-expansion-reuse-649','gamma1-integral-descent-643-before-explicit-coefficient-transport','gamma1-regularity-643-before-order-name-repair','gamma1-regularity-643-before-field-independent-order-consumer']
evidence=sorted(set(evidence))
for n in evidence+folders:assert (p/n).exists(),n
s=s[:a]+'evidence=[p/'+repr(routefile)+']\nevidence += [p/n for n in '+repr(evidence)+']\nfor folder in '+repr(folders)+':\n    evidence += sorted(f for f in (p/folder).rglob("*") if f.is_file())\n'+s[b:]
oldedge='  GAMMAONEDIFF8335["Exact geometric H1 with original coefficient action; actual curve/scalar fields and both cusp differential integral equations proved. Regularity, full differential/Picard/H1/diamond comparison, original finite-character Galois realization and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
newedge='  GAMMAONEDIFF8335["Exact geometric H1, actual fields and both integral equations (DUB-17/18)"] --> GAMMAONEREG8360\n  GAMMAONEREG8360["Actual Gamma1 cusp-matching differentials are regular; original Fricke transformation, holomorphy, torsion cyclotomic Fourier coefficients and cusp bounds proved. Rational spanning, realization, converse, Picard/H1/diamond, arithmetic realization and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
s=re.sub(r'^edge = .+$',lambda _:'edge = '+repr(oldedge),s,flags=re.M)
s=re.sub(r'^arch.write_text\(.*$',lambda _:"arch.write_text(arch.read_text(encoding='utf-8').replace(edge,"+repr(newedge)+"),encoding='utf-8')",s,flags=re.M)
s=re.sub(r'^    "promotionChanges": .+$',lambda _:'    "promotionChanges": '+repr('Only scratch imports are qualified. Every audited statement, proof body and comment is preserved. Actual Gamma1 fields and native cusp forms retain their definitions; no regularity or integral equation is assumed. No source contract is weakened.')+',',s,flags=re.M)
logline = '  logInfo m!"SOURCE GAMMA ONE REGULARITY FRICKE INPUTS AUDIT PASS: {count} theorems including private/generated declarations. Actual Gamma1 cusp-matching differentials are regular; original Fricke transformations, holomorphy and cyclotomic Fourier coefficients are proved. Rational spanning, realization, converse and arithmetic comparison remain; 16/20 gates."\n'
a=s.index("b = re.sub(r'  logInfo")
b=s.index(", b)",a)+len(", b)")
s=s[:a]+"b = re.sub("+repr('  logInfo m!".*"\n')+", "+repr(logline)+", b)"+s[b:]
output('integrate_source_gamma_one_regularity_fricke_inputs_8360.py',s)
scripts=['integrate_source_gamma_one_regularity_fricke_inputs_8360.py']
for stem in ['prepare_gamma_one_differential_inputs_production_ownership','prepare_gamma_one_differential_inputs_scratch_ownership','compare_gamma_one_differential_inputs_ownership','prepare_gamma_one_differential_inputs_global_ownership']:
 s=tr((p/(stem+'_8335.py')).read_text(encoding='utf-8'))
 s=re.sub(r'\b138\b','264',s).replace('All 19 mathematical','All 25 mathematical').replace('len(names)==len(certs)==8','len(names)==len(certs)==4')
 n=tr(stem+'_8335.py');output(n,s);scripts.append(n)
s=tr((p/'record_source_gamma_one_differential_inputs_8335.py').read_text(encoding='utf-8'))
s=re.sub(r'\b138\b','264',s)
s=s.replace('== 19','== 25').replace('"incrementModules": 19','"incrementModules": 25').replace('"linterScopes": 19','"linterScopes": 25')
s=s.replace('len(ownershipComparison["scopes"]) == 8','len(ownershipComparison["scopes"]) == 4')
s=s.replace('Eight declaration-value audits verify 136 required dependencies.','Four declaration-value audits verify 162 required dependencies.').replace('int(a[2]) == 24024','int(a[2]) == 24150')
n='record_source_gamma_one_regularity_fricke_inputs_8360.py';output(n,s);scripts.append(n)
for stem in ['build_gamma_one_differential_inputs','verify_gamma_one_differential_inputs']:
 n=tr(stem+'_8335.ps1');output(n,tr((p/(stem+'_8335.ps1')).read_text(encoding='utf-8')));scripts.append(n)
n='archive_gamma_one_regularity_fricke_inputs_canonical_8360.py';output(n,tr((p/'archive_gamma_one_differential_inputs_canonical_8335.py').read_text(encoding='utf-8')));scripts.append(n)
for n in scripts:
 f=p/n;t=f.read_text(encoding='utf-8')
 if f.suffix=='.py':ast.parse(t)
 assert '16/22' not in t and 'DUB-17-22' not in t,f
output('gamma-one-regularity-fricke-inputs-preexecution-review-8360.json',json.dumps(dict(status='Prepared; require 8335 canonical PASS and archive before integration.',route=routefile,routeSha256=sha(p/routefile),modules=25,queries=152,theorems=126,constructions=26,exhaustiveScratchChecks=264,proofValueEdges=162,scopes=4,receipts=digests,expectedConsumers=24150,expectedConstructions=2351,fullGoal='16/20; DUB-17--20 OPEN; all 20 gates unchanged.',scripts=[dict(path=str(p/n),sha256=sha(p/n)) for n in scripts],productionMutation=False),indent=2)+'\n')
print(json.dumps(dict(scripts=len(scripts),modules=25,productionMutation=False)))
