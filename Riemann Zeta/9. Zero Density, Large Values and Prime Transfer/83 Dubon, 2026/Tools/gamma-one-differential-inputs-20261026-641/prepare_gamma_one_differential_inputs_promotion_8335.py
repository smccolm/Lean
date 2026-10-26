from pathlib import Path
import ast,json,re,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
names=['source-gamma-one-geometric-subgroup-1','source-gamma-one-geometric-cohomology-1','source-gamma-one-hecke-coefficient-1','source-gamma-one-curve-geometry-2','source-gamma-one-scalar-extension-1','source-gamma-one-field-modular-ratio-2','source-gamma-one-differential-finite-integral-5','source-gamma-one-differential-cusp-integral-6']
certs=[json.loads((p/(n+'-scratch-receipt.json')).read_text(encoding='utf-8')) for n in names]
digests={n+'-scratch-receipt.json':sha(p/(n+'-scratch-receipt.json')) for n in names}
mods=sum(len(c['modules']) for c in certs);queries=sum(len(c['queries']) for c in certs)
ths=sum(len(c['theoremRegistrations']) for c in certs);defs=sum(len(c['constructionRegistrations']) for c in certs)
checks=sum(c['exhaustiveTheorems'] for c in certs);edges=sum(c['requiredProofValueEdges'] for c in certs)
assert (mods,queries,ths,defs,checks,edges)==(19,85,73,12,138,136)
routefile='gamma-one-differential-inputs-promotion-route-641.json'
archive='Tools/gamma-one-differential-inputs-20261026-641'
dependency='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero Galois association -> arithmetic realization of original finite Gamma1 Hecke characters -> actual Picard/H1, full/parabolic and diamond comparison retaining the original homogeneous coefficient endomorphism -> exact geometric H1 correspondence, actual curve and regular differential/cusp comparison.'
discharged='The actual upper and geometric Hecke subgroups are explicitly isomorphic with the original conjugation and analytic matrix action. Native H1 pullback/trace gives exactly the original finite Hecke operator, including its homogeneous coefficient endomorphism, and this action factors on either side of the geometric operator. Existing finite-coordinate curve results establish local differential generators, canonical divisors and injective expansions for the actual Gamma1 and Hecke fields. Literal scalar extension equals the complex integral-ratio field; every element has a same-weight complex modular quotient with nonzero denominator. This does not assert the reverse membership of arbitrary complex modular quotients. Native analytic differentiation and the existing level-one dimension theorem construct a nonzero q-Euler normalization scalar. For an actual weight-two cusp form f and Y*qEuler(j)=qExpansion(f), the finite expression Y^6*j^4*(j-1728)^3 is integral over C[j]; for positive M with Gamma(M) contained in the group, the cusp expression Y^(2M)*j^(M+1)*(j-1728)^M is integral over C[1/j]. Existing modular norms and level-one polynomial reduction, plus native cusp exponential decay, prove both integral equations without assuming them.'
boundary='The valuation deduction of regularity, algebraic differential realization and converse cusp construction remain. The actual Picard/H1, full/parabolic, transpose and diamond comparison must still identify the original finite homogeneous-coefficient Hecke characters with geometric characters. Frobenius/inertia, arithmetic realization of these characters, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain required. Neither complex semisimplicity, finite characters, Witt coefficients nor a universal deformation ring supplies a characteristic-zero lift or point. 16/20; DUB-17--20 OPEN.'
route='The renewed search is recorded in Dubon Reuse Search 2026-10-26.md; deeper fixed-revision differential inputs are archived here. Reuse native H1 composition and original coset sums, existing finite-coordinate curve/canonical theorems, literal Laurent scalar extension and native modular quotient operations. Use the existing bounded derivative and level-one weight-14 dimension theorem rather than a new Ramanujan system. Cubing permits reuse of the existing weight-12 modular orbit polynomial for the inverse-j bound; no second interpolation construction is needed. Native cusp decay constructs f^(2M)*E4^3/Delta. Preserve the constructed nonzero scalar instead of proving an unnecessary exact normalization. A restriction-unfolding recursion-depth diagnostic is preserved; explicit coefficient identities resolve it with unchanged limits. No external project was built or imported; root pins and all twenty gates are unchanged.'
status='The actual Gamma1 H1 and differential-input chain passes 138 exhaustive scratch checks and 85 explicit public axiom queries across 19 modules, with sixteen linters per module and zero diagnostics. Eight declaration-value audits verify 136 required dependencies. Production aggregate, focused audit and sequential foundation/paper verification of the 8,335-module scope are pending.'
def output(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output(routefile,json.dumps(dict(scope=641,scopeIds=[627,629,631,632,634,636,638,640],receipts=digests,dependency=dependency,discharged=discharged,remaining=boundary,route=route,precedingCanonicalScope=8316,rootPinsChanged=False,proofLimitsChanged=False,externalImport=False,fullGoal='16/20; DUB-17--20 OPEN; all 20 acceptance gates unchanged.',reason='Require preceding canonical PASS and immutable archive before production mutation.'),indent=2)+'\n')
repl={
'gamma-one-arithmetic-geometry-promotion-route-626.json':routefile,
'Tools/gamma-one-arithmetic-geometry-20261026-626':archive,
'Tools/primitive-gamma-one-hecke-20261026-618':'Tools/gamma-one-arithmetic-geometry-20261026-626',
'appliedSourceGammaOneArithmeticGeometry':'appliedSourceGammaOneDifferentialInputs',
'appliedSourcePrimitiveGammaOneHeckeRealization':'appliedSourceGammaOneArithmeticGeometry',
'SourceGammaOneArithmeticGeometry':'SourceGammaOneDifferentialInputs',
'gamma_one_arithmetic_geometry':'gamma_one_differential_inputs',
'source-gamma-one-arithmetic-geometry':'source-gamma-one-differential-inputs',
'SOURCE GAMMA ONE ARITHMETIC GEOMETRY':'SOURCE GAMMA ONE DIFFERENTIAL INPUTS',
'actual Gamma1 arithmetic geometry and Hecke equivariance':'actual Gamma1 cohomology and differential inputs',
'Actual Gamma1 arithmetic geometry and Hecke equivariance':'Actual Gamma1 cohomology and differential inputs',
'8,316':'8,335','8,290':'8,316','8316':'8335','8290':'8316'}
rx=re.compile('|'.join(map(re.escape,sorted(repl,key=len,reverse=True))))
tr=lambda s:rx.sub(lambda m:repl[m[0]],s)
s=tr((p/'integrate_source_gamma_one_arithmetic_geometry_8316.py').read_text(encoding='utf-8'))
s=re.sub(r'^digests = .+$',lambda _:'digests = '+repr(digests),s,flags=re.M)
s=s.replace('(26, 26, 102, 77, 25)','(19, 19, 85, 73, 12)').replace('count == 185','count == 138').replace('"increment": 26, "queries": 102','"increment": 19, "queries": 85')
for k,v in [('dependency',dependency),('discharged',discharged),('boundary',boundary),('route',route),('status',status)]:
 s=re.sub(r'^'+k+r' = .+$',lambda _,k=k,v=v:k+' = '+repr(v),s,flags=re.M)
a=s.index('evidence=[p/');b=s.index("for cert in certs:\n    evidence.append",a)
evidence=list(digests)
for c in certs:
 for field in ['log','dependencyAuditLog']:evidence += [Path(c[field]).with_suffix(x).name for x in ['.lean','.log','.exit']]
 review=json.loads(Path(c['reuseReview']).read_text(encoding='utf-8'))
 evidence.append(Path(review['routeAssessment']['path']).name)
for i in [627,629,631,632,633,634,635,636,637,638,639,640]:
 evidence += [f.name for f in p.iterdir() if f.is_file() and f.suffix in ['.py','.json','.txt'] and re.search(r'(?<!\d)'+str(i)+r'[a-z]?(?:\.|-)',f.name)]
for n in names:evidence.append(n+'-audit-config.json')
folders=['gamma1-differential-input-reuse-633','gamma1-differential-prerequisite-reuse-635','gamma1-qeuler-reuse-637','gamma1-cusp-integral-reuse-639','gamma1-inverse-j-640-before-explicit-coefficient-rewrite']
for n in set(evidence):assert (p/n).exists(),n
s=s[:a]+'evidence=[p/'+repr(routefile)+']\nevidence += [p/n for n in '+repr(sorted(set(evidence)))+']\nfor folder in '+repr(folders)+':\n    evidence += sorted(f for f in (p/folder).rglob("*") if f.is_file())\n'+s[b:]
oldedge='  GAMMAONEFIELDS8316["Actual Gamma1 fields, finite maps, Picard Hecke and arithmetic equivariance proved. Original homogeneous-coefficient H1/diamond comparison, Frobenius/inertia, all-weight Galois realization and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
newedge='  GAMMAONEFIELDS8316["Actual Gamma1 fields, finite maps, Picard Hecke and arithmetic equivariance (DUB-17/18)"] --> GAMMAONEDIFF8335\n  GAMMAONEDIFF8335["Exact geometric H1 with original coefficient action; actual curve/scalar fields and both cusp differential integral equations proved. Regularity, full differential/Picard/H1/diamond comparison, original finite-character Galois realization and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
s=re.sub(r'^edge = .+$',lambda _:'edge = '+repr(oldedge),s,flags=re.M)
s=re.sub(r'^arch.write_text\(.*$',lambda _:"arch.write_text(arch.read_text(encoding='utf-8').replace(edge,"+repr(newedge)+"),encoding='utf-8')",s,flags=re.M)
s=re.sub(r'^    "promotionChanges": .+$',lambda _:'    "promotionChanges": '+repr('Only scratch imports are qualified. Every audited statement, proof body and comment is preserved. Original coefficient endomorphisms, literal q-expansion fields, genuine modular forms and both integral equations retain their definitions. No source contract is weakened.')+',',s,flags=re.M)
a=s.index("    '  logInfo m!");b=s.index("', b)",a)
s=s[:a]+'    \'  logInfo m!"SOURCE GAMMA ONE DIFFERENTIAL INPUTS AUDIT PASS: {count} theorems including private/generated declarations. Exact geometric H1 retains the original coefficient action; actual curve/scalar fields and both differential integral equations are proved. Regularity, full differential/Picard/H1/diamond comparison, arithmetic realization and higher continuation remain required; 16/20 gates."\\n'+s[b:]
s=s.replace('gives its verification status','gives its verification status')
output('integrate_source_gamma_one_differential_inputs_8335.py',s)
for stem in ['prepare_gamma_one_arithmetic_geometry_production_ownership','prepare_gamma_one_arithmetic_geometry_scratch_ownership','compare_gamma_one_arithmetic_geometry_ownership','prepare_gamma_one_arithmetic_geometry_global_ownership']:
 s=tr((p/(stem+'_8316.py')).read_text(encoding='utf-8'))
 s=re.sub(r'\b185\b','138',s).replace('All 26 mathematical','All 19 mathematical').replace('len(names)==len(certs)==4','len(names)==len(certs)==8')
 output(tr(stem+'_8316.py'),s)
s=tr((p/'record_source_gamma_one_arithmetic_geometry_8316.py').read_text(encoding='utf-8'))
s=re.sub(r'\b185\b','138',s)
s=s.replace('t.count("All linting checks passed!") == 26','t.count("All linting checks passed!") == 19').replace('len(k["modules"]) == 26','len(k["modules"]) == 19')
s=s.replace('"incrementModules": 26','"incrementModules": 19').replace('"linterScopes": 26','"linterScopes": 19')
s=s.replace('len(ownershipComparison["scopes"]) == 4','len(ownershipComparison["scopes"]) == 8')
s=s.replace('Four declaration-value audits verify 144 required dependencies.','Eight declaration-value audits verify 136 required dependencies.').replace('int(a[2]) == 23951','int(a[2]) == 24024')
s=s.replace('assert f"all {cert[\'requiredProofValueEdges\']} required proof" in dt','assert re.search(r"all " + str(cert["requiredProofValueEdges"]) + r" required (?:proof )?dependencies", dt)')
output('record_source_gamma_one_differential_inputs_8335.py',s)
for stem in ['build_gamma_one_arithmetic_geometry','verify_gamma_one_arithmetic_geometry']:
 output(tr(stem+'_8316.ps1'),tr((p/(stem+'_8316.ps1')).read_text(encoding='utf-8')))
output('archive_gamma_one_differential_inputs_canonical_8335.py',tr((p/'archive_gamma_one_arithmetic_geometry_canonical_8316.py').read_text(encoding='utf-8')))
scripts=[f for f in p.iterdir() if re.search(r'8335\.(py|ps1)$',f.name)]
for f in scripts:
 t=f.read_text(encoding='utf-8')
 if f.suffix=='.py':ast.parse(t)
 assert '16/22' not in t and 'DUB-17-22' not in t,f
review=dict(status='Prepared; require 8316 canonical PASS, immutable archive and renewed-search publication before integration.',route=routefile,routeSha256=sha(p/routefile),modules=mods,queries=queries,theorems=ths,constructions=defs,exhaustiveScratchChecks=checks,proofValueEdges=edges,scopes=8,receipts=digests,expectedConsumers=24024,expectedConstructions=2325,fullGoal='16/20; DUB-17--20 OPEN; all 20 gates unchanged.',sourceBodies='Audited statements, bodies and comments unchanged; only scratch project imports qualified.',scripts=[dict(path=str(f),sha256=sha(f)) for f in scripts],productionMutation=False)
output('gamma-one-differential-inputs-preexecution-review-8335.json',json.dumps(review,indent=2)+'\n')
print(json.dumps(dict(scripts=len(scripts),modules=mods,queries=queries,exhaustive=checks,edges=edges,productionMutation=False)))
