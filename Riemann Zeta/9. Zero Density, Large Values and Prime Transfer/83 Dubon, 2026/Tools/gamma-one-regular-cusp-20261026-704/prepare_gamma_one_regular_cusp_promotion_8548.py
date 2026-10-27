from pathlib import Path
import ast,json,re,hashlib
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
names=['source-gamma-one-local-holomorphy-12-scratch-receipt.json','source-gamma-one-cusp-vanishing-10-scratch-receipt.json','source-gamma-one-fourier-converse-2-scratch-receipt.json','source-gamma-one-linear-comparison-2-scratch-receipt.json']
certs=[json.loads((p/n).read_text(encoding='utf-8')) for n in names]
digests={n:sha(p/n) for n in names}
assert tuple(sum(len(c[k]) for c in certs) for k in ['modules','queries','theoremRegistrations','constructionRegistrations'])==(26,80,69,11)
assert sum(c['exhaustiveTheorems'] for c in certs)==132
assert sum(c['requiredProofValueEdges'] for c in certs)==116
routefile='gamma-one-regular-cusp-promotion-route-704.json'
archive='Tools/gamma-one-regular-cusp-20261026-704'
dependency='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> arithmetic realization of original finite Gamma1 Hecke characters -> actual Picard/H1, full/parabolic, transpose and diamond comparison retaining the original homogeneous coefficient endomorphism -> actual regular-differential/cusp equivalence with literal Fourier normalization.'
discharged='The actual original complex Gamma1 regular differential space is now linearly equivalent to native weight-two cusp forms, with exact equality of their literal Fourier expansions. Actual modular quotient germs define normalized finite and cusp places. Original regularity and exact j-derivative orders give finite holomorphy and positive order at every cusp, deriving all analytic and decay hypotheses. The existing modular q-Euler identity removes the precise 2*pi*i factor. The proved differential spanning theorem covers every regular differential. Both Fourier realization directions and injectivity identify the actual linear ranges; no dimension formula, matching-series witness or cusp-form-existence assumption is supplied.'
boundary='The actual Picard/H1, full/parabolic, transpose and diamond comparison must still identify original finite homogeneous-coefficient Hecke characters with geometric characters. Exact analytic period normalization and compatibility with the original Hecke/diamond operators remain. Coefficient-field transport is still required wherever used by the arithmetic comparison. Frobenius/inertia, arithmetic realization of those characters, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain. The full all-weight arithmetic goal is unchanged. Complex semisimplicity, finite characters, Witt coefficients and universal deformation rings do not supply a characteristic-zero lift or point. 16/20; DUB-17--20 OPEN.'
route='The renewed selected-file search is recorded in Dubon Reuse Search 2026-10-26.md. Reuse actual modular ratios, normalized place construction, exact local differential orders, native removable singularities, the existing j-derivative and q-Euler identities, original integral Fourier spanning and differential expansion injectivity. This gives the required complex equivalence without a new global Gamma1 ramification classification, cusp-width dictionary, numerical degree bound, period-germ framework or dimension formula. The external comparison files were inspected at the pinned commit; their full import closure was not built or certified. Only audited mathematical sources are promoted and only imports are qualified. Failed variants and audit/helper evidence remain preserved. Pins, proof limits, frozen source and all twenty acceptance gates are unchanged.'
status='The actual complex Gamma1 regular-differential/cusp equivalence passes 132 exhaustive scratch theorem checks and 80 public axiom queries across 26 modules, with sixteen linters per module and zero diagnostics. Four declaration-value audits verify 116 required dependencies. Production aggregate, focused audit and sequential foundation/paper verification of the 8,548-module scope are pending.'
def output(n,s):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(s)
output(routefile,json.dumps(dict(scope=704,scopeIds=['700','701','702','703'],receipts=digests,dependency=dependency,discharged=discharged,remaining=boundary,route=route,precedingCanonicalScope=8522,rootPinsChanged=False,proofLimitsChanged=False,externalImport=False,fullGoal='16/20; DUB-17--20 OPEN; all 20 gates unchanged.',reason='Require preceding canonical PASS and immutable archive before production mutation.'),indent=2)+'\n')
repl={'gamma-one-integral-differential-promotion-route-699.json':routefile,'Tools/gamma-one-integral-differential-20261026-699':archive,'Tools/gamma-one-rational-fourier-20261026-692':'Tools/gamma-one-integral-differential-20261026-699','appliedSourceGammaOneIntegralDifferential':'appliedSourceGammaOneRegularCusp','appliedSourceGammaOneRationalFourier':'appliedSourceGammaOneIntegralDifferential','SourceGammaOneIntegralDifferential':'SourceGammaOneRegularCusp','gamma_one_integral_differential':'gamma_one_regular_cusp','source-gamma-one-integral-differential':'source-gamma-one-regular-cusp','SOURCE GAMMA ONE INTEGRAL DIFFERENTIAL':'SOURCE GAMMA ONE REGULAR CUSP','actual Gamma1 integral Fourier spanning and differential realization':'actual Gamma1 regular-differential/cusp equivalence','Actual Gamma1 integral Fourier spanning and differential realization':'Actual Gamma1 regular-differential/cusp equivalence','8,522':'8,548','8,493':'8,522','8522':'8548','8493':'8522'}
rx=re.compile('|'.join(map(re.escape,sorted(repl,key=len,reverse=True))))
tr=lambda s:rx.sub(lambda m:repl[m[0]],s)
s=tr((p/'integrate_source_gamma_one_integral_differential_8522.py').read_text(encoding='utf-8'))
s=s.replace('paper-verification-8522-console.exit','paper-verification-8522b-console.exit')
s=re.sub(r'^digests = .+$',lambda _:'digests = '+repr(digests),s,flags=re.M)
s=s.replace('(29, 29, 68, 63, 5)','(26, 26, 80, 69, 11)').replace('count == 91','count == 132').replace('"increment": 29, "queries": 68','"increment": 26, "queries": 80')
for k,v in [('dependency',dependency),('discharged',discharged),('boundary',boundary),('route',route),('status',status)]:
 assert re.search(r'^'+k+r' = .+$',s,re.M),k
 s=re.sub(r'^'+k+r' = .+$',lambda _,k=k,v=v:k+' = '+repr(v),s,flags=re.M)
a=s.index('evidence=[p/');b=s.index("for cert in certs:\n    evidence.append",a)
evidence=list(names)
for cert in certs:
 for key in ['log','dependencyAuditLog']:
  f=Path(cert[key]);evidence += [f.with_suffix(ext).name for ext in ['.lean','.log','.exit']]
 review=json.loads(Path(cert['reuseReview']).read_text(encoding='utf-8'));evidence.append(Path(review['routeAssessment']['path']).name)
for f in p.iterdir():
 if f.is_file() and f.suffix in ['.json','.py','.ps1','.txt','.log','.exit'] and re.search(r'(?<!\d)(700|701|702|703)[a-z]?(?:\.|-)',f.name):evidence.append(f.name)
evidence += [n.replace('-scratch-receipt.json','-audit-config.json') for n in names]
owners=['SourceGammaOneLocalHolomorphyScratchOwnership700','SourceGammaOneCuspVanishingScratchOwnership701','SourceGammaOneFourierConverseScratchOwnership702','SourceGammaOneLinearComparisonScratchOwnership703']
for stem in owners:evidence += [stem+ext for ext in ['.lean','.log','.exit']]
folders=['gamma-one-converse-core-reuse-698']+[f.name for f in p.iterdir() if f.is_dir() and re.search(r'(700|701|702|703)[a-z]?$',f.name)]
assert len(folders)==19,folders
for n in evidence+folders:assert (p/n).exists(),n
s=s[:a]+'evidence=[p/'+repr(routefile)+']\nevidence += [p/n for n in '+repr(sorted(set(evidence)))+']\nfor folder in '+repr(folders)+':\n    evidence += sorted(f for f in (p/folder).rglob("*") if f.is_file())\n'+s[b:]
oldedge='  GAMMAONEINTEGRAL8522["Actual integral Fourier spanning and coefficient-field-valued cusp to regular differential realization proved. Converse, Picard/H1/diamond, original all-weight association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
newedge='  GAMMAONEINTEGRAL8522["Actual integral Fourier spanning and coefficient-field-valued cusp to regular differential realization (DUB-17/18)"] --> GAMMAONEREGULAR8548\n  GAMMAONEREGULAR8548["Actual complex Gamma1 regular-differential/cusp linear equivalence with exact Fourier normalization proved. Original Hecke/diamond/Picard/H1, all-weight arithmetic association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
assert (r/'Dubon Architecture.md').read_text(encoding='utf-8').count(oldedge)==1
s=re.sub(r'^edge = .+$',lambda _:'edge = '+repr(oldedge),s,flags=re.M)
s=re.sub(r'^arch.write_text\(.*$',lambda _:"arch.write_text(arch.read_text(encoding='utf-8').replace(edge,"+repr(newedge)+"),encoding='utf-8')",s,flags=re.M)
s=re.sub(r'^    "promotionChanges": .+$',lambda _:'    "promotionChanges": '+repr('Only scratch imports are qualified. All final audited statements, proof bodies and comments remain identical. The original function field, actual regular differentials, native cusp forms, literal Fourier series and exact complex normalization are retained. No source contract is weakened.')+',',s,flags=re.M)
a=s.index("b = re.sub('  logInfo");b=s.index(', b)',a)+len(', b)')
logline='  logInfo m!"SOURCE GAMMA ONE REGULAR CUSP AUDIT PASS: {count} theorems including private/generated declarations. The actual complex Gamma1 regular-differential/cusp linear equivalence and literal Fourier identity are proved. Original Hecke/diamond/Picard/H1 arithmetic comparison remains; 16/20 gates."\n'
s=s[:a]+'b = re.sub('+repr('  logInfo m!".*"\n')+', '+repr(logline)+', b)'+s[b:]
output('integrate_source_gamma_one_regular_cusp_8548.py',s)
scripts=['integrate_source_gamma_one_regular_cusp_8548.py']
for stem in ['prepare_gamma_one_integral_differential_production_ownership','prepare_gamma_one_integral_differential_global_ownership']:
 n=tr(stem+'_8522.py');output(n,tr((p/(stem+'_8522.py')).read_text(encoding='utf-8')));scripts.append(n)
s=tr((p/'compare_gamma_one_integral_differential_ownership_8522.py').read_text(encoding='utf-8'))
s=s.replace('len(names)==len(certs)==2','len(names)==len(certs)==4').replace('len(allmods)==len(set(allmods))==29','len(allmods)==len(set(allmods))==26').replace("result['scratchSum']==91","result['scratchSum']==132").replace('All 29 mathematical','All 26 mathematical')
n='compare_gamma_one_regular_cusp_ownership_8548.py';output(n,s);scripts.append(n)
s=tr((p/'record_source_gamma_one_integral_differential_8522.py').read_text(encoding='utf-8'))
s=re.sub(r'\b91\b','132',s);s=re.sub(r'== 29\b','== 26',s);s=re.sub(r'== 2\b','== 4',s)
s=s.replace('"incrementModules": 29','"incrementModules": 26').replace('"linterScopes": 29','"linterScopes": 26').replace('Two declaration-value audits verify 87 required dependencies.','Four declaration-value audits verify 116 required dependencies.').replace('int(a[2]) == 24650','int(a[2]) == 24719')
n='record_source_gamma_one_regular_cusp_8548.py';output(n,s);scripts.append(n)
for stem in ['verify_gamma_one_integral_differential','build_gamma_one_integral_differential']:
 n=tr(stem+'_8522.ps1');output(n,tr((p/(stem+'_8522.ps1')).read_text(encoding='utf-8')));scripts.append(n)
n='archive_gamma_one_regular_cusp_canonical_8548.py';output(n,tr((p/'archive_gamma_one_integral_differential_canonical_8522.py').read_text(encoding='utf-8')));scripts.append(n)
output('source-gamma-one-regular-cusp-scratch-ownership-8548.json',json.dumps(owners,indent=2)+'\n')
for n in scripts:
 if (p/n).suffix=='.py':ast.parse((p/n).read_text(encoding='utf-8'))
output('gamma-one-regular-cusp-preexecution-review-8548.json',json.dumps(dict(status='Prepared; require 8522 canonical PASS and archive before integration.',route=routefile,routeSha256=sha(p/routefile),modules=26,queries=80,theorems=69,constructions=11,exhaustiveScratchChecks=132,proofValueEdges=116,scopes=4,receipts=digests,expectedConsumers=24719,expectedConstructions=2456,fullGoal='16/20; DUB-17--20 OPEN; all 20 gates unchanged.',scripts=[dict(path=str(p/n),sha256=sha(p/n)) for n in scripts],productionMutation=False),indent=2)+'\n')
print(json.dumps(dict(scripts=len(scripts),modules=26,checks=132,archivedFailureAndReuseFolders=len(folders),productionMutation=False)))