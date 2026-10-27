from pathlib import Path
import ast,json,re,hashlib
p=Path(r'E:\Lean\.tmp\dubon83');r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
names=['source-fricke-cyclotomic-analytic-transport-5-scratch-receipt.json','source-gamma-one-cyclotomic-conjugation-13-scratch-receipt.json','source-gamma-one-rational-cusp-span-4-scratch-receipt.json']
certs=[json.loads((p/n).read_text(encoding='utf-8')) for n in names]
digests={n:sha(p/n) for n in names}
assert tuple(sum(len(c[k]) for c in certs) for k in ['modules','queries','theoremRegistrations','constructionRegistrations'])==(22,63,58,5)
checks=sum(c['exhaustiveTheorems'] for c in certs);edges=sum(c['requiredProofValueEdges'] for c in certs)
assert (checks,edges)==(89,87)
routefile='gamma-one-rational-fourier-promotion-route-692.json';archive='Tools/gamma-one-rational-fourier-20261026-692'
dependency='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> arithmetic realization of original finite Gamma1 Hecke characters -> actual Picard/H1, full/parabolic, transpose and diamond comparison retaining the original homogeneous coefficient endomorphism -> actual differential/cusp comparison -> rational Fourier spanning of actual Gamma1 cusp forms.'
discharged='The actual cyclotomic torsion-index permutation preserves the original Laurent generated field and j-integrality; the existing holomorphic representative theorem constructs actual conjugate Fricke fractions. Integral modular lifts and original Gamma1 translations prove modular covariance and preserve level invariance. Laurent order transports all-cusp vanishing. Holomorphic division in the original fraction algebra preserves both elliptic divisibility conditions through actual j and j-1728 coordinates. The exact cusp characterization constructs another actual cusp form of the same weight and level, and rational Eisenstein/discriminant cancellation identifies its literal width-one coefficients with their cyclotomic conjugates. The original coefficient field is finite Galois over Q. Actual trace sums have rational Fourier coefficients, and the pinned Mathlib trace-dual basis reconstructs each original-image generator. The already proved original-image spanning theorem therefore yields rational Fourier spanning of the full Gamma1 weight-two cusp-form space at every nonzero level. General weights retain the explicit source balance k+4a+6b=12m; weight two uses a=b=m=1.'
boundary='Rational Fourier spanning is proved, but bounded denominators for the original integral-ratio function field remain. Arbitrary Gamma1 cusp differential realization and the converse regular-differential construction remain. The actual Picard/H1, full/parabolic, transpose and diamond comparison must identify original finite homogeneous-coefficient Hecke characters with geometric characters. Frobenius/inertia, arithmetic realization of those characters, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain. No unrestricted odd-weight weight-lowering claim is made, and the all-weight arithmetic goal is unchanged. Complex semisimplicity, finite characters, Witt coefficients and universal deformation rings do not supply a characteristic-zero lift or point. 16/20; DUB-17--20 OPEN.'
route='The renewed selected-file search is recorded in Dubon Reuse Search 2026-10-26.md. Reuse the original Laurent integral representative instead of the external rational-at-infinity and recursive Fourier-division packages. Use the proved SL2 reduction lift and local Gamma1 translation lift for covariance, the original cusp characterization for analytic reconstruction, and exact Laurent germs for coefficients. Construct conjugates only for the original-image generating set, which already spans; defer the unnecessary stronger conjugation theorem for every cyclotomic-coefficient form. Native trace-dual basis reconstruction replaces the external Dedekind-independence and matrix-invertibility proof. No external full import closure was built or certified. Failed audit/helper evidence and retained failed source variants are preserved. Only audited mathematical sources are promoted and only imports are qualified. Pins, proof limits, source contract and all twenty acceptance gates are unchanged.'
status=f'The rational Fourier spanning chain passes {checks} exhaustive scratch theorem checks and 63 public axiom queries across 22 modules, with sixteen linters per module and zero diagnostics. Three declaration-value audits verify 87 required dependencies. Production aggregate, focused audit and sequential foundation/paper verification of the 8,493-module scope are pending.'
def output(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output(routefile,json.dumps(dict(scope=692,scopeIds=['687','688','689'],receipts=digests,dependency=dependency,discharged=discharged,remaining=boundary,route=route,precedingCanonicalScope=8471,rootPinsChanged=False,proofLimitsChanged=False,externalImport=False,fullGoal='16/20; DUB-17--20 OPEN; all 20 acceptance gates unchanged.',reason='Require preceding canonical PASS and immutable archive before production mutation.'),indent=2)+'\n')
repl={'cusp-cyclotomic-spanning-promotion-route-685.json':routefile,'Tools/cusp-cyclotomic-spanning-20261026-685':archive,'Tools/fricke-cyclotomic-fourier-span-20261026-673':'Tools/cusp-cyclotomic-spanning-20261026-685','appliedSourceCuspCyclotomicSpanning':'appliedSourceGammaOneRationalFourier','appliedSourceFrickeCyclotomicFourierSpan':'appliedSourceCuspCyclotomicSpanning','SourceCuspCyclotomicSpanning':'SourceGammaOneRationalFourier','cusp_cyclotomic_spanning':'gamma_one_rational_fourier','source-cusp-cyclotomic-spanning':'source-gamma-one-rational-fourier','SOURCE CUSP CYCLOTOMIC SPANNING':'SOURCE GAMMA ONE RATIONAL FOURIER','actual cyclotomic cusp-form spanning':'actual Gamma1 rational Fourier spanning','Actual cyclotomic cusp-form spanning':'Actual Gamma1 rational Fourier spanning','8,471':'8,493','8,432':'8,471','8471':'8493','8432':'8471'}
rx=re.compile('|'.join(map(re.escape,sorted(repl,key=len,reverse=True))));tr=lambda s:rx.sub(lambda m:repl[m[0]],s)
s=tr((p/'integrate_source_cusp_cyclotomic_spanning_8471.py').read_text(encoding='utf-8'))
s=re.sub(r'^digests = .+$',lambda _:'digests = '+repr(digests),s,flags=re.M)
s=s.replace('(39, 39, 117, 102, 15)','(22, 22, 63, 58, 5)').replace('count == 174','count == 89').replace('"increment": 39, "queries": 117','"increment": 22, "queries": 63')
for k,v in [('dependency',dependency),('discharged',discharged),('boundary',boundary),('route',route),('status',status)]:s=re.sub(r'^'+k+r' = .+$',lambda _,k=k,v=v:k+' = '+repr(v),s,flags=re.M)
a=s.index('evidence=[p/');b=s.index("for cert in certs:\n    evidence.append",a)
evidence=list(digests)
for cert in certs:
 for key in ['log','dependencyAuditLog']:
  f=Path(cert[key]);evidence += [f.with_suffix(ext).name for ext in ['.lean','.log','.exit']]
 review=json.loads(Path(cert['reuseReview']).read_text(encoding='utf-8'));evidence.append(Path(review['routeAssessment']['path']).name)
for f in p.iterdir():
 if f.is_file() and f.suffix in ['.json','.py','.ps1','.txt'] and re.search(r'(?<!\d)(686|687|688|689)[a-z]?(?:\.|-)',f.name):evidence.append(f.name)
for n in names:evidence.append(n.replace('-scratch-receipt.json','-audit-config.json'))
evidence += ['source-gamma-one-cyclotomic-conjugation-13-audit-config-v2.json','SourceGammaOneCyclotomicConjugationDependencyAudit13.lean','SourceGammaOneCyclotomicConjugationDependencyAudit13.log','SourceGammaOneCyclotomicConjugationDependencyAudit13.exit']
folders=['fricke-laurent-field-conjugation-api-687a','cyclotomic-cancellation-api-failed-688a','cyclotomic-transport-pretrim-688b','gamma-one-trace-api-failed-689a','gamma-one-cyclotomic-transport-inputs-reuse-686']
evidence=sorted(set(evidence))
for n in evidence+folders:assert (p/n).exists(),n
s=s[:a]+'evidence=[p/'+repr(routefile)+']\nevidence += [p/n for n in '+repr(evidence)+']\nfor folder in '+repr(folders)+':\n    evidence += sorted(f for f in (p/folder).rglob("*") if f.is_file())\n'+s[b:]
oldedge='  CUSPCYCLOTOMIC8471["Actual cusp-image twist stability, full fixed-field descent and cyclotomic Fourier spanning of Gamma1 weight-two cusp forms proved. Rational descent over Q, bounded denominators, differential realization/converse, Picard/H1/diamond, original all-weight association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
newedge='  CUSPCYCLOTOMIC8471["Actual cusp-image twist stability and cyclotomic Fourier spanning (DUB-17/18)"] --> GAMMAONERATIONAL8493\n  GAMMAONERATIONAL8493["Actual same-level cyclotomic cusp conjugates and rational Fourier spanning of Gamma1 weight-two cusp forms proved. Bounded denominators, differential realization/converse, Picard/H1/diamond, original all-weight association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
s=re.sub(r'^edge = .+$',lambda _:'edge = '+repr(oldedge),s,flags=re.M)
s=re.sub(r'^arch.write_text\(.*$',lambda _:"arch.write_text(arch.read_text(encoding='utf-8').replace(edge,"+repr(newedge)+"),encoding='utf-8')",s,flags=re.M)
s=re.sub(r'^    "promotionChanges": .+$',lambda _:'    "promotionChanges": '+repr('Only scratch imports are qualified. Every final audited statement, proof body and comment is preserved. The original cyclotomic field, actual Fricke fractions, integral modular lifts, original E4/E6/Delta factors, same-level cusp forms, literal Fourier coefficients and native trace-dual reconstruction remain explicit. No source contract is weakened.')+',',s,flags=re.M)
logline='  logInfo m!"SOURCE GAMMA ONE RATIONAL FOURIER AUDIT PASS: {count} theorems including private/generated declarations. Actual same-level cyclotomic cusp conjugates and rational Fourier spanning of Gamma1 weight-two cusp forms are proved. Bounded denominators, differential realization and arithmetic comparison remain; 16/20 gates."\n'
a=s.index("b = re.sub('  logInfo");b=s.index(', b)',a)+len(', b)');s=s[:a]+'b = re.sub('+repr('  logInfo m!".*"\n')+', '+repr(logline)+', b)'+s[b:]
output('integrate_source_gamma_one_rational_fourier_8493.py',s)
scripts=['integrate_source_gamma_one_rational_fourier_8493.py']
for stem in ['prepare_cusp_cyclotomic_spanning_production_ownership','prepare_cusp_cyclotomic_spanning_scratch_ownership','compare_cusp_cyclotomic_spanning_ownership','prepare_cusp_cyclotomic_spanning_global_ownership']:
 s=tr((p/(stem+'_8471.py')).read_text(encoding='utf-8'));s=re.sub(r'\b174\b','89',s).replace('All 39 mathematical','All 22 mathematical')
 n=tr(stem+'_8471.py');output(n,s);scripts.append(n)
s=tr((p/'record_source_cusp_cyclotomic_spanning_8471.py').read_text(encoding='utf-8'))
s=re.sub(r'\b174\b','89',s).replace('== 39','== 22').replace('"incrementModules": 39','"incrementModules": 22').replace('"linterScopes": 39','"linterScopes": 22').replace('== 7','== 3')
s=s.replace('Seven declaration-value audits verify 168 required dependencies.','Three declaration-value audits verify 87 required dependencies.').replace('int(a[2]) == 24529','int(a[2]) == 24587')
n='record_source_gamma_one_rational_fourier_8493.py';output(n,s);scripts.append(n)
for stem in ['build_cusp_cyclotomic_spanning','verify_cusp_cyclotomic_spanning']:
 n=tr(stem+'_8471.ps1');output(n,tr((p/(stem+'_8471.ps1')).read_text(encoding='utf-8')));scripts.append(n)
n='archive_gamma_one_rational_fourier_canonical_8493.py';output(n,tr((p/'archive_cusp_cyclotomic_spanning_canonical_8471.py').read_text(encoding='utf-8')));scripts.append(n)
for n in scripts:
 f=p/n;t=f.read_text(encoding='utf-8')
 if f.suffix=='.py':ast.parse(t)
 assert '16/22' not in t and 'DUB-17-22' not in t,f
output('gamma-one-rational-fourier-preexecution-review-8493.json',json.dumps(dict(status='Prepared; require 8471 canonical PASS and archive before integration.',route=routefile,routeSha256=sha(p/routefile),modules=22,queries=63,theorems=58,constructions=5,exhaustiveScratchChecks=89,proofValueEdges=87,scopes=3,receipts=digests,expectedConsumers=24587,expectedConstructions=2440,fullGoal='16/20; DUB-17--20 OPEN; all 20 gates unchanged.',scripts=[dict(path=str(p/n),sha256=sha(p/n)) for n in scripts],productionMutation=False),indent=2)+'\n')
print(json.dumps(dict(scripts=len(scripts),modules=22,checks=89,productionMutation=False)))
