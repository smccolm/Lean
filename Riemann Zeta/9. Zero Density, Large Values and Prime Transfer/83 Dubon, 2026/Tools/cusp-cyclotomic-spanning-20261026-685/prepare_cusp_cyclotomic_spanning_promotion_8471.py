from pathlib import Path
import ast,json,re,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
names=['source-fricke-laurent-independence-2-scratch-receipt.json','source-fricke-coefficient-twist-8-scratch-receipt.json','source-fricke-twist-modular-algebra-5-scratch-receipt.json','source-fricke-elliptic-divisibility-5-scratch-receipt.json','source-fricke-cusp-image-stability-9-scratch-receipt.json','source-cusp-fricke-rational-span-7-scratch-receipt.json','source-gamma-one-cyclotomic-cusp-span-3-scratch-receipt.json']
certs=[json.loads((p/n).read_text(encoding='utf-8')) for n in names]
digests={n:sha(p/n) for n in names}
assert tuple(sum(len(c[k]) for c in certs) for k in ['modules','queries','theoremRegistrations','constructionRegistrations'])==(39,117,102,15)
checks=sum(c['exhaustiveTheorems'] for c in certs)
edges=sum(c['requiredProofValueEdges'] for c in certs)
assert edges==168
routefile='cusp-cyclotomic-spanning-promotion-route-685.json'
archive='Tools/cusp-cyclotomic-spanning-20261026-685'
dependency='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> arithmetic realization of original finite Gamma1 Hecke characters -> actual Picard/H1, full/parabolic, transpose and diamond comparison retaining the original homogeneous coefficient endomorphism -> actual differential/cusp comparison -> rational cusp-form spanning -> cyclotomic Fourier spanning and original weight-image descent.'
discharged='Laurent coefficient independence gives a complex basis of the original cyclotomic Fricke span. Its coefficient twist fixes original fractions, commutes with actual modular pullbacks, preserves products and powers, and transports discriminant cusp orders. Holomorphic quotient closure derives the needed elliptic divisibility transport. The exact original E4/E6/Delta weight-image criterion is proved by local monic division and analytic gluing, and every elliptic, cusp and subgroup premise is derived for the twisted image, producing an actual cusp form of the same weight and subgroup. The full algebraically closed fixed-coefficient theorem and finite-support subspace descent are proved and applied to the actual stable image. Injective pullback gives spanning by original cyclotomic Fricke weight images. Laurent division by the proved nonzero Eisenstein factor identifies the original cusp-form Fourier coefficients. Thus the actual Gamma1 weight-two cusp-form space is spanned over the complex numbers by forms whose width-one Fourier coefficients lie in the original cyclotomic field. The general result retains the explicit source balance k+4a+6b=12m; weight two uses a=b=m=1.'
boundary='Cyclotomic Fourier spanning is not yet rational Fourier spanning over Q: nontrivial cyclotomic coefficient conjugation and rational descent remain, as do bounded denominators for the original integral-ratio field. Arbitrary Gamma1 cusp differential realization and the converse regular-differential construction remain. The actual Picard/H1, full/parabolic, transpose and diamond comparison must identify original finite homogeneous-coefficient Hecke characters with geometric characters. Frobenius/inertia, arithmetic realization of those characters, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain. No unrestricted odd-weight weight-lowering claim is made, and the all-weight arithmetic goal is unchanged. Complex semisimplicity, finite characters, Witt coefficients and universal deformation rings do not supply a characteristic-zero lift or point. 16/20; DUB-17--20 OPEN.'
route='The renewed selected-file search is recorded in Dubon Reuse Search 2026-10-26.md. Reuse actual Laurent germs and analytic injectivity to construct the coefficient twist directly on the original Fricke span, avoiding the external general flatness construction. Holomorphic quotient closure replaces the external monic-growth route for elliptic divisibility. Adapt only the necessary fixed-field, finite-support descent and local cusp-image arguments from the frozen primary sources; native linear algebra pulls the span back. Existing rational Eisenstein and discriminant expansions identify Fourier coefficients by Laurent uniqueness, avoiding recursive unit-division infrastructure. No external full import closure was built or certified. All used and failed audit/helper evidence and retained failed source variants are preserved; only audited mathematical sources are promoted and only imports are qualified. Pins, proof limits, source contract and all twenty acceptance gates are unchanged.'
status=f'The cyclotomic cusp spanning chain passes {checks} exhaustive scratch theorem checks and 117 public axiom queries across 39 modules, with sixteen linters per module and zero diagnostics. Seven declaration-value audits verify 168 required dependencies. Production aggregate, focused audit and sequential foundation/paper verification of the 8,471-module scope are pending.'
def output(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output(routefile,json.dumps(dict(scope=685,scopeIds=['674','675','676','677','680','683','684'],receipts=digests,dependency=dependency,discharged=discharged,remaining=boundary,route=route,precedingCanonicalScope=8432,rootPinsChanged=False,proofLimitsChanged=False,externalImport=False,fullGoal='16/20; DUB-17--20 OPEN; all 20 acceptance gates unchanged.',reason='Require preceding canonical PASS and immutable archive before production mutation.'),indent=2)+'\n')
repl={'fricke-cyclotomic-fourier-span-promotion-route-673.json':routefile,'Tools/fricke-cyclotomic-fourier-span-20261026-673':archive,'Tools/fricke-rational-structure-inputs-20261026-664':'Tools/fricke-cyclotomic-fourier-span-20261026-673','appliedSourceFrickeCyclotomicFourierSpan':'appliedSourceCuspCyclotomicSpanning','appliedSourceFrickeRationalStructureInputs':'appliedSourceFrickeCyclotomicFourierSpan','SourceFrickeCyclotomicFourierSpan':'SourceCuspCyclotomicSpanning','fricke_cyclotomic_fourier_span':'cusp_cyclotomic_spanning','source-fricke-cyclotomic-fourier-span':'source-cusp-cyclotomic-spanning','SOURCE FRICKE CYCLOTOMIC FOURIER SPAN':'SOURCE CUSP CYCLOTOMIC SPANNING','actual Fricke cyclotomic Fourier span':'actual cyclotomic cusp-form spanning','Actual Fricke cyclotomic Fourier span':'Actual cyclotomic cusp-form spanning','8,432':'8,471','8,390':'8,432','8432':'8471','8390':'8432'}
rx=re.compile('|'.join(map(re.escape,sorted(repl,key=len,reverse=True))))
tr=lambda s:rx.sub(lambda m:repl[m[0]],s)
s=tr((p/'integrate_source_fricke_cyclotomic_fourier_span_8432.py').read_text(encoding='utf-8'))
s=re.sub(r'^digests = .+$',lambda _:'digests = '+repr(digests),s,flags=re.M)
s=s.replace('(42, 42, 154, 137, 17)','(39, 39, 117, 102, 15)').replace('count == 189','count == '+str(checks)).replace('"increment": 42, "queries": 154','"increment": 39, "queries": 117')
for k,v in [('dependency',dependency),('discharged',discharged),('boundary',boundary),('route',route),('status',status)]:s=re.sub(r'^'+k+r' = .+$',lambda _,k=k,v=v:k+' = '+repr(v),s,flags=re.M)
a=s.index('evidence=[p/');b=s.index("for cert in certs:\n    evidence.append",a)
evidence=list(digests)
for cert in certs:
 for key in ['log','dependencyAuditLog']:
  f=Path(cert[key]);evidence += [f.with_suffix(ext).name for ext in ['.lean','.log','.exit']]
 review=json.loads(Path(cert['reuseReview']).read_text(encoding='utf-8'))
 evidence.append(Path(review['routeAssessment']['path']).name)
for f in p.iterdir():
 if f.is_file() and f.suffix in ['.json','.py','.ps1','.txt'] and re.search(r'(?<!\d)(674|675|676|677|678|679|680|681|682|683|684)[a-z]?(?:\.|-)',f.name):evidence.append(f.name)
for n in names:evidence.append(n.replace('-scratch-receipt.json','-audit-config.json'))
folders=['fricke-scalar-basis-api-failed-675a','fricke-scalar-basis-instance-failed-675b','fricke-elliptic-power-route-superseded-677a','cusp-weight-transformation-preparer-failed-679a','cusp-fricke-span-api-failed-683a','eisenstein-factor-laurent-diagnostic-684a','fricke-cusp-descent-inputs-reuse-678']
evidence=sorted(set(evidence))
for n in evidence+folders:assert (p/n).exists(),n
s=s[:a]+'evidence=[p/'+repr(routefile)+']\nevidence += [p/n for n in '+repr(evidence)+']\nfor folder in '+repr(folders)+':\n    evidence += sorted(f for f in (p/folder).rglob("*") if f.is_file())\n'+s[b:]
oldedge='  FRICKEFOURIER8432["Original-constant Laurent integral descent, holomorphic summand realization and pole-cleared cyclotomic Fourier span proved. Rational cusp spanning, differential realization, converse, Picard/H1/diamond, original arithmetic association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
newedge='  FRICKEFOURIER8432["Original-constant Laurent descent and actual holomorphic Fricke span (DUB-17/18)"] --> CUSPCYCLOTOMIC8471\n  CUSPCYCLOTOMIC8471["Actual cusp-image twist stability, full fixed-field descent and cyclotomic Fourier spanning of Gamma1 weight-two cusp forms proved. Rational descent over Q, bounded denominators, differential realization/converse, Picard/H1/diamond, original all-weight association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
s=re.sub(r'^edge = .+$',lambda _:'edge = '+repr(oldedge),s,flags=re.M)
s=re.sub(r'^arch.write_text\(.*$',lambda _:"arch.write_text(arch.read_text(encoding='utf-8').replace(edge,"+repr(newedge)+"),encoding='utf-8')",s,flags=re.M)
s=re.sub(r'^    "promotionChanges": .+$',lambda _:'    "promotionChanges": '+repr('Only scratch imports are qualified. Every final audited statement, proof body and comment is preserved. Original cyclotomic fields, actual Fricke functions, E4/E6/Delta factors, cusp forms, modular pullbacks and width-one q-expansions remain explicit. No source contract is weakened.')+',',s,flags=re.M)
logline='  logInfo m!"SOURCE CUSP CYCLOTOMIC SPANNING AUDIT PASS: {count} theorems including private/generated declarations. Actual cusp-image twist stability, fixed-field descent and Gamma1 cyclotomic Fourier spanning are proved. Rational descent, differential realization and arithmetic comparison remain; 16/20 gates."\n'
a=s.index("b = re.sub('  logInfo");b=s.index(', b)',a)+len(', b)')
s=s[:a]+'b = re.sub('+repr('  logInfo m!".*"\n')+', '+repr(logline)+', b)'+s[b:]
output('integrate_source_cusp_cyclotomic_spanning_8471.py',s)
scripts=['integrate_source_cusp_cyclotomic_spanning_8471.py']
for stem in ['prepare_fricke_cyclotomic_fourier_span_production_ownership','prepare_fricke_cyclotomic_fourier_span_scratch_ownership','compare_fricke_cyclotomic_fourier_span_ownership','prepare_fricke_cyclotomic_fourier_span_global_ownership']:
 s=tr((p/(stem+'_8432.py')).read_text(encoding='utf-8'))
 s=re.sub(r'\b189\b',str(checks),s).replace('All 42 mathematical','All 39 mathematical')
 n=tr(stem+'_8432.py');output(n,s);scripts.append(n)
s=tr((p/'record_source_fricke_cyclotomic_fourier_span_8432.py').read_text(encoding='utf-8'))
s=re.sub(r'\b189\b',str(checks),s).replace('== 42','== 39').replace('"incrementModules": 42','"incrementModules": 39').replace('"linterScopes": 42','"linterScopes": 39')
s=s.replace('Seven declaration-value audits verify 225 required dependencies.','Seven declaration-value audits verify 168 required dependencies.').replace('int(a[2]) == 24427','int(a[2]) == 24529')
n='record_source_cusp_cyclotomic_spanning_8471.py';output(n,s);scripts.append(n)
for stem in ['build_fricke_cyclotomic_fourier_span','verify_fricke_cyclotomic_fourier_span']:
 n=tr(stem+'_8432.ps1');output(n,tr((p/(stem+'_8432.ps1')).read_text(encoding='utf-8')));scripts.append(n)
n='archive_cusp_cyclotomic_spanning_canonical_8471.py';output(n,tr((p/'archive_fricke_cyclotomic_fourier_span_canonical_8432.py').read_text(encoding='utf-8')));scripts.append(n)
for n in scripts:
 f=p/n;t=f.read_text(encoding='utf-8')
 if f.suffix=='.py':ast.parse(t)
 assert '16/22' not in t and 'DUB-17-22' not in t,f
output('cusp-cyclotomic-spanning-preexecution-review-8471.json',json.dumps(dict(status='Prepared; require 8432 canonical PASS and archive before integration.',route=routefile,routeSha256=sha(p/routefile),modules=39,queries=117,theorems=102,constructions=15,exhaustiveScratchChecks=checks,proofValueEdges=168,scopes=7,receipts=digests,expectedConsumers=24529,expectedConstructions=2435,fullGoal='16/20; DUB-17--20 OPEN; all 20 gates unchanged.',scripts=[dict(path=str(p/n),sha256=sha(p/n)) for n in scripts],productionMutation=False),indent=2)+'\n')
print(json.dumps(dict(scripts=len(scripts),modules=39,checks=checks,productionMutation=False)))
