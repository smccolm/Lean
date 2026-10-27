from pathlib import Path
import ast,json,re,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
names=['source-fricke-cyclotomic-descent-10-scratch-receipt.json','source-algebraic-constant-integral-span-5-scratch-receipt.json','source-transcendental-constant-integral-span-7e-scratch-receipt.json','source-laurent-integral-constant-span-6-scratch-receipt.json','source-actual-fricke-laurent-integral-span-4-scratch-receipt.json','source-fricke-holomorphic-integral-span-8-scratch-receipt.json','source-fricke-pole-cleared-fourier-span-2-scratch-receipt.json']
certs=[json.loads((p/n).read_text(encoding='utf-8')) for n in names]
digests={n:sha(p/n) for n in names}
assert tuple(sum(len(c[k]) for c in certs) for k in ['modules','queries','theoremRegistrations','constructionRegistrations'])==(42,154,137,17)
checks=sum(c['exhaustiveTheorems'] for c in certs)
edges=sum(c['requiredProofValueEdges'] for c in certs)
assert edges==225
routefile='fricke-cyclotomic-fourier-span-promotion-route-673.json'
archive='Tools/fricke-cyclotomic-fourier-span-20261026-673'
dependency='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> arithmetic realization of original finite Gamma1 Hecke characters -> actual Picard/H1, full/parabolic, transpose and diamond comparison retaining the original homogeneous coefficient endomorphism -> actual differential/cusp comparison -> rational cusp-form spanning -> pole-cleared cyclotomic Fourier span of actual Fricke functions.'
discharged='The original cyclotomic j/Fricke functions and their fractions have literal Laurent cusp representations. Coefficient retraction descends monic equations to the original field. Algebraic and transcendental simple-constant extensions, finite constant capture and coefficient-derived relative transcendence prove the integral Laurent span over the original constants. The actual finite Fricke generator family satisfies every finiteness, integrality, coefficient-field and transcendence premise. Integral Laurent summands lift to actual cyclotomic fractions; their cleared monic equations and the existing removable-singularity theorem derive holomorphic representatives. Native coefficientwise complex scalar multiplication and analytic uniqueness lift the Laurent span to actual functions. Positive discriminant cusp order clears each summand pole, and uniqueness against the cyclotomic Laurent expansion proves every resulting Fourier coefficient lies in the original cyclotomic field. Hence a holomorphic principal-level invariant function with the required bounds at every modular translate lies in the complex span of actual holomorphic functions with pole-cleared cyclotomic Fourier coefficients.'
boundary='Rational cusp-form spanning still requires the modular-weight, cusp-condition and coefficient-descent steps. The pole-cleared weight-zero function span does not yet realize an arbitrary Gamma1 cusp form as an original algebraic differential; the converse regular-differential-to-cusp construction also remains. The actual Picard/H1, full/parabolic, transpose and diamond comparison must identify original finite homogeneous-coefficient Hecke characters with geometric characters. Frobenius/inertia, arithmetic realization of those characters, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain. Complex semisimplicity, finite characters, Witt coefficients and universal deformation rings do not supply a characteristic-zero lift or point. 16/20; DUB-17--20 OPEN.'
route='The renewed selected-file search is recorded in Dubon Reuse Search 2026-10-26.md. Adapt the fixed-revision primary simple-constant integral-span proofs to the actual Laurent field, deriving the relative transcendence premise from coefficients. Reuse native fraction-ring surjectivity, the existing expanded-j transcendence, finite-action monic relation, analytic cusp-germ injectivity, coefficient retraction, monic-root bound and removable-singularity extension. For Fourier coefficients, native meromorphic orders clear the cusp pole and existing Laurent representations identify coefficients directly; the external general valuation engine, analytic quotient file, recursive Fourier division and monic-growth development are unnecessary on this route. All used and failed audits, original failed source variants and fresh successors are retained. Only final audited sources are promoted and only imports are qualified. No external full import closure was built or certified; pins, proof limits, source contract and all twenty acceptance gates are unchanged.'
status=f'The cyclotomic Fourier span passes {checks} exhaustive scratch theorem checks and 154 public axiom queries across 42 modules, with sixteen linters per module and zero diagnostics. Seven declaration-value audits verify 225 required dependencies. Production aggregate, focused audit and sequential foundation/paper verification of the 8,432-module scope are pending.'
def output(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output(routefile,json.dumps(dict(scope=673,scopeIds=['665','666','667e','669','670','671','672'],receipts=digests,dependency=dependency,discharged=discharged,remaining=boundary,route=route,precedingCanonicalScope=8390,rootPinsChanged=False,proofLimitsChanged=False,externalImport=False,fullGoal='16/20; DUB-17--20 OPEN; all 20 acceptance gates unchanged.',reason='Require preceding canonical PASS and immutable archive before production mutation.'),indent=2)+'\n')
repl={'fricke-rational-structure-inputs-promotion-route-664.json':routefile,'Tools/fricke-rational-structure-inputs-20261026-664':archive,'Tools/gamma-one-regularity-fricke-inputs-20261026-653':'Tools/fricke-rational-structure-inputs-20261026-664','appliedSourceFrickeRationalStructureInputs':'appliedSourceFrickeCyclotomicFourierSpan','appliedSourceGammaOneRegularityFrickeInputs':'appliedSourceFrickeRationalStructureInputs','SourceFrickeRationalStructureInputs':'SourceFrickeCyclotomicFourierSpan','fricke_rational_structure_inputs':'fricke_cyclotomic_fourier_span','source-fricke-rational-structure-inputs':'source-fricke-cyclotomic-fourier-span','SOURCE FRICKE RATIONAL STRUCTURE INPUTS':'SOURCE FRICKE CYCLOTOMIC FOURIER SPAN','actual Fricke rational-structure inputs':'actual Fricke cyclotomic Fourier span','Actual Fricke rational-structure inputs':'Actual Fricke cyclotomic Fourier span','8,390':'8,432','8,360':'8,390','8390':'8432','8360':'8390'}
rx=re.compile('|'.join(map(re.escape,sorted(repl,key=len,reverse=True))))
tr=lambda s:rx.sub(lambda m:repl[m[0]],s)
s=tr((p/'integrate_source_fricke_rational_structure_inputs_8390.py').read_text(encoding='utf-8'))
s=re.sub(r'^digests = .+$',lambda _:'digests = '+repr(digests),s,flags=re.M)
s=s.replace('(30, 30, 192, 140, 52)','(42, 42, 154, 137, 17)').replace('count == 262','count == '+str(checks)).replace('"increment": 30, "queries": 192','"increment": 42, "queries": 154')
for k,v in [('dependency',dependency),('discharged',discharged),('boundary',boundary),('route',route),('status',status)]:s=re.sub(r'^'+k+r' = .+$',lambda _,k=k,v=v:k+' = '+repr(v),s,flags=re.M)
a=s.index('evidence=[p/');b=s.index("for cert in certs:\n    evidence.append",a)
evidence=list(digests)
for cert in certs:
 for key in ['log','dependencyAuditLog']:
  f=Path(cert[key]);evidence += [f.with_suffix(ext).name for ext in ['.lean','.log','.exit']]
 review=json.loads(Path(cert['reuseReview']).read_text(encoding='utf-8'))
 evidence.append(Path(review['routeAssessment']['path']).name)
for f in p.iterdir():
 if f.is_file() and f.suffix in ['.json','.py','.ps1','.txt'] and re.search(r'(?<!\d)(665|666|667|668|669|670|671|672)[a-z]?(?:\.|-)',f.name):evidence.append(f.name)
for n in names:evidence.append(n.replace('-scratch-receipt.json','-audit-config.json'))
for pat in ['SourceTranscendentalConstant*','SourceLaurentIntegralConstantSpanAudit6*','SourceLaurentIntegralConstantSpanDependencyAudit6*','SourceFrickeHolomorphicIntegralSpanAudit8*','SourceFrickeHolomorphicIntegralSpanDependencyAudit8*','LaurentIntegralSpanTypeProbe669*','SourceTranscendentalConstantDiscovery667*']:
 evidence += [f.name for f in p.glob(pat) if f.is_file() and f.suffix in ['.lean','.log','.exit']]
folders=['transcendental-constant-integral-span-failed-667a','transcendental-constant-field-range-failed-667b','transcendental-constant-pretrim-667c']
evidence=sorted(set(evidence))
for n in evidence+folders:assert (p/n).exists(),n
s=s[:a]+'evidence=[p/'+repr(routefile)+']\nevidence += [p/n for n in '+repr(evidence)+']\nfor folder in '+repr(folders)+':\n    evidence += sorted(f for f in (p/folder).rglob("*") if f.is_file())\n'+s[b:]
oldedge='  FRICKERAT8390["Actual cyclotomic transport, Fricke separation, fixed field C(j), stable-family fraction realization and monic relations proved. Rational spanning, differential realization, converse, Picard/H1/diamond, original arithmetic realization and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
newedge='  FRICKERAT8390["Actual Fricke fixed field, stable-family fractions and monic relations (DUB-17/18)"] --> FRICKEFOURIER8432\n  FRICKEFOURIER8432["Original-constant Laurent integral descent, holomorphic summand realization and pole-cleared cyclotomic Fourier span proved. Rational cusp spanning, differential realization, converse, Picard/H1/diamond, original arithmetic association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
s=re.sub(r'^edge = .+$',lambda _:'edge = '+repr(oldedge),s,flags=re.M)
s=re.sub(r'^arch.write_text\(.*$',lambda _:"arch.write_text(arch.read_text(encoding='utf-8').replace(edge,"+repr(newedge)+"),encoding='utf-8')",s,flags=re.M)
s=re.sub(r'^    "promotionChanges": .+$',lambda _:'    "promotionChanges": '+repr('Only scratch imports are qualified. Every final audited statement, proof body and comment is preserved. Original cyclotomic fields, Laurent series, actual Fricke functions, modular orbits and the ordinary coefficientwise complex scalar action remain explicit. No source contract is weakened.')+',',s,flags=re.M)
logline='  logInfo m!"SOURCE FRICKE CYCLOTOMIC FOURIER SPAN AUDIT PASS: {count} theorems including private/generated declarations. Original-constant integral Laurent descent, holomorphic summand realization and pole-cleared cyclotomic Fourier span are proved. Rational cusp spanning, differential realization and arithmetic comparison remain; 16/20 gates."\n'
a=s.index("b = re.sub('  logInfo");b=s.index(', b)',a)+len(', b)')
s=s[:a]+'b = re.sub('+repr('  logInfo m!".*"\n')+', '+repr(logline)+', b)'+s[b:]
output('integrate_source_fricke_cyclotomic_fourier_span_8432.py',s)
scripts=['integrate_source_fricke_cyclotomic_fourier_span_8432.py']
for stem in ['prepare_fricke_rational_structure_inputs_production_ownership','prepare_fricke_rational_structure_inputs_scratch_ownership','compare_fricke_rational_structure_inputs_ownership','prepare_fricke_rational_structure_inputs_global_ownership']:
 s=tr((p/(stem+'_8390.py')).read_text(encoding='utf-8'))
 s=re.sub(r'\b262\b',str(checks),s).replace('All 30 mathematical','All 42 mathematical').replace('len(names)==len(certs)==8','len(names)==len(certs)==7')
 n=tr(stem+'_8390.py');output(n,s);scripts.append(n)
s=tr((p/'record_source_fricke_rational_structure_inputs_8390.py').read_text(encoding='utf-8'))
s=re.sub(r'\b262\b',str(checks),s).replace('== 30','== 42').replace('"incrementModules": 30','"incrementModules": 42').replace('"linterScopes": 30','"linterScopes": 42')
s=s.replace('len(ownershipComparison["scopes"]) == 8','len(ownershipComparison["scopes"]) == 7').replace('Eight declaration-value audits verify 224 required dependencies.','Seven declaration-value audits verify 225 required dependencies.').replace('int(a[2]) == 24290','int(a[2]) == 24427')
n='record_source_fricke_cyclotomic_fourier_span_8432.py';output(n,s);scripts.append(n)
for stem in ['build_fricke_rational_structure_inputs','verify_fricke_rational_structure_inputs']:
 n=tr(stem+'_8390.ps1');output(n,tr((p/(stem+'_8390.ps1')).read_text(encoding='utf-8')));scripts.append(n)
n='archive_fricke_cyclotomic_fourier_span_canonical_8432.py';output(n,tr((p/'archive_fricke_rational_structure_inputs_canonical_8390.py').read_text(encoding='utf-8')));scripts.append(n)
for n in scripts:
 f=p/n;t=f.read_text(encoding='utf-8')
 if f.suffix=='.py':ast.parse(t)
 assert '16/22' not in t and 'DUB-17-22' not in t,f
output('fricke-cyclotomic-fourier-span-preexecution-review-8432.json',json.dumps(dict(status='Prepared; require 8390 canonical PASS and archive before integration.',route=routefile,routeSha256=sha(p/routefile),modules=42,queries=154,theorems=137,constructions=17,exhaustiveScratchChecks=checks,proofValueEdges=225,scopes=7,receipts=digests,expectedConsumers=24427,expectedConstructions=2420,fullGoal='16/20; DUB-17--20 OPEN; all 20 gates unchanged.',scripts=[dict(path=str(p/n),sha256=sha(p/n)) for n in scripts],productionMutation=False),indent=2)+'\n')
print(json.dumps(dict(scripts=len(scripts),modules=42,checks=checks,productionMutation=False)))