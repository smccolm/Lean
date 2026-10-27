from pathlib import Path
import ast, json, re, hashlib

p = Path(__file__).parent
r = Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
names = ['source-gamma-one-integral-cusp-span-23-scratch-receipt.json',
         'source-gamma-one-cusp-differential-realization-6-scratch-receipt.json']
certs = [json.loads((p/n).read_text(encoding='utf-8')) for n in names]
digests = {n: sha(p/n) for n in names}
assert tuple(sum(len(c[k]) for c in certs) for k in
             ['modules', 'queries', 'theoremRegistrations', 'constructionRegistrations']) == (29, 68, 63, 5)
assert sum(c['exhaustiveTheorems'] for c in certs) == 91
assert sum(c['requiredProofValueEdges'] for c in certs) == 87
routefile = 'gamma-one-integral-differential-promotion-route-699.json'
archive = 'Tools/gamma-one-integral-differential-20261026-699'
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> arithmetic realization of original finite Gamma1 Hecke characters -> actual Picard/H1, full/parabolic, transpose and diamond comparison retaining the original homogeneous coefficient endomorphism -> actual differential/cusp comparison -> integral Fourier spanning and regular differential realization of actual Gamma1 weight-two cusp forms.'
discharged = 'Every rational Fourier coefficient sequence of an actual Gamma1 cusp form satisfying the source weight balance has a single nonzero integer denominator. The proof derives the original cyclotomic Fricke-field membership and monic equation, bounds the actual torsion Weierstrass numerators, descends a nonzero bounded fraction by the native field trace, and uses native Laurent-series integral closure. Exact integral Eisenstein units and the discriminant cancel the weight factors. Rational spanning therefore yields integral Fourier spanning of the entire actual Gamma1 weight-two cusp space. The existing complex j-derivative identity descends to an integral identity with a proved nonzero integer normalization. Actual same-weight integral modular ratios then construct the differential coefficient for every integral cusp generator. Coefficientwise span descent realizes every cusp form whose coefficients lie in the given field embedding as an actual differential on the original integral-ratio Gamma1 function field. Over an algebraically closed coefficient field the already proved local regularity criterion makes this differential regular. No bounded-denominator, field-membership, monic-relation or differential-existence assumption remains in these consumers.'
boundary = 'The converse from an actual regular Gamma1 differential to an actual cusp form remains. The actual Picard/H1, full/parabolic, transpose and diamond comparison must identify original finite homogeneous-coefficient Hecke characters with geometric characters. Frobenius/inertia, arithmetic realization of those characters, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain. General-weight denominator and spanning statements retain the explicit balance k+4a+6b=12m; weight two derives it with a=b=m=1. The full all-weight arithmetic goal is unchanged. Complex semisimplicity, finite characters, Witt coefficients and universal deformation rings do not supply a characteristic-zero lift or point. 16/20; DUB-17--20 OPEN.'
route = 'The renewed selected-file search is recorded in Dubon Reuse Search 2026-10-26.md. Reuse the original Laurent field, native normality under localization, native trace and the proved rational cusp span. This avoids the unused power-series-only route and the external recursive coefficient division. Construct the differential directly as a multiple of D(j); reuse the existing exact complex derivative formula, integral-ratio field and regularity criterion, avoiding a new differential-expansion framework. The pinned external arguments supplied finite denominator scaling and the geometric comparison route; their full import closure was not built or certified. Only audited mathematical sources are promoted and only imports are qualified. Failed variants and audit/helper evidence remain preserved. Pins, proof limits, frozen source and all twenty acceptance gates are unchanged.'
status = 'The integral Fourier spanning and forward differential realization chain passes 91 exhaustive scratch theorem checks and 68 public axiom queries across 29 modules, with sixteen linters per module and zero diagnostics. Two declaration-value audits verify 87 required dependencies. Production aggregate, focused audit and sequential foundation/paper verification of the 8,522-module scope are pending.'

def output(n, s):
    with (p/n).open('x', encoding='utf-8', newline='\n') as f:
        f.write(s)

output(routefile, json.dumps(dict(scope=699, scopeIds=['696','697'], receipts=digests,
    dependency=dependency, discharged=discharged, remaining=boundary, route=route,
    precedingCanonicalScope=8493, rootPinsChanged=False, proofLimitsChanged=False,
    externalImport=False, fullGoal='16/20; DUB-17--20 OPEN; all 20 gates unchanged.',
    reason='Require preceding canonical PASS and immutable archive before production mutation.'), indent=2)+'\n')
repl = {
    'gamma-one-rational-fourier-promotion-route-692.json': routefile,
    'Tools/gamma-one-rational-fourier-20261026-692': archive,
    'Tools/cusp-cyclotomic-spanning-20261026-685': 'Tools/gamma-one-rational-fourier-20261026-692',
    'appliedSourceGammaOneRationalFourier': 'appliedSourceGammaOneIntegralDifferential',
    'appliedSourceCuspCyclotomicSpanning': 'appliedSourceGammaOneRationalFourier',
    'SourceGammaOneRationalFourier': 'SourceGammaOneIntegralDifferential',
    'gamma_one_rational_fourier': 'gamma_one_integral_differential',
    'source-gamma-one-rational-fourier': 'source-gamma-one-integral-differential',
    'SOURCE GAMMA ONE RATIONAL FOURIER': 'SOURCE GAMMA ONE INTEGRAL DIFFERENTIAL',
    'actual Gamma1 rational Fourier spanning': 'actual Gamma1 integral Fourier spanning and differential realization',
    'Actual Gamma1 rational Fourier spanning': 'Actual Gamma1 integral Fourier spanning and differential realization',
    '8,493': '8,522', '8,471': '8,493', '8493': '8522', '8471': '8493'}
rx = re.compile('|'.join(map(re.escape, sorted(repl,key=len,reverse=True))))
tr = lambda s: rx.sub(lambda m: repl[m[0]], s)
s = tr((p/'integrate_source_gamma_one_rational_fourier_8493.py').read_text(encoding='utf-8'))
s = re.sub(r'^digests = .+$', lambda _: 'digests = '+repr(digests), s, flags=re.M)
s = s.replace('(22, 22, 63, 58, 5)', '(29, 29, 68, 63, 5)').replace('count == 89', 'count == 91')
s = s.replace('"increment": 22, "queries": 63', '"increment": 29, "queries": 68')
for k,v in [('dependency',dependency),('discharged',discharged),('boundary',boundary),('route',route),('status',status)]:
    s = re.sub(r'^'+k+r' = .+$', lambda _,k=k,v=v: k+' = '+repr(v), s, flags=re.M)
a=s.index('evidence=[p/'); b=s.index("for cert in certs:\n    evidence.append", a)
evidence=list(names)
for cert in certs:
    for key in ['log','dependencyAuditLog']:
        f=Path(cert[key]); evidence += [f.with_suffix(ext).name for ext in ['.lean','.log','.exit']]
    review=json.loads(Path(cert['reuseReview']).read_text(encoding='utf-8'))
    evidence.append(Path(review['routeAssessment']['path']).name)
for f in p.iterdir():
    if f.is_file() and f.suffix in ['.json','.py','.ps1','.txt'] and re.search(r'(?<!\d)(690|691|693|694|695|696|697)[a-z]?(?:\.|-)',f.name):
        evidence.append(f.name)
evidence += [n.replace('-scratch-receipt.json','-audit-config.json') for n in names]
evidence += ['SourceGammaOneIntegralCuspSpanAudit23.lean','SourceGammaOneIntegralCuspSpanAudit23.log','SourceGammaOneIntegralCuspSpanAudit23.exit']
for stem in ['SourceGammaOneIntegralCuspScratchOwnership696','SourceGammaOneIntegralCuspScratchOwnership696V2','SourceGammaOneCuspDifferentialScratchOwnership697']:
    evidence += [stem+ext for ext in ['.lean','.log','.exit']]
folders=['gamma-one-bounded-denominator-core-reuse-690','bounded-denominator-series-inputs-reuse-690b',
    'deferred-power-series-route-696','integral-cusp-linter-failure-696b',
    'integer-j-normalization-failed-697a','gamma-one-differential-realization-failed-697b',
    'scratch-name-collision-695']
for n in evidence+folders: assert (p/n).exists(), n
s=s[:a]+'evidence=[p/'+repr(routefile)+']\nevidence += [p/n for n in '+repr(sorted(set(evidence)))+']\nfor folder in '+repr(folders)+':\n    evidence += sorted(f for f in (p/folder).rglob("*") if f.is_file())\n'+s[b:]
oldedge='  GAMMAONERATIONAL8493["Actual same-level cyclotomic cusp conjugates and rational Fourier spanning of Gamma1 weight-two cusp forms proved. Bounded denominators, differential realization/converse, Picard/H1/diamond, original all-weight association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
newedge='  GAMMAONERATIONAL8493["Actual same-level cyclotomic cusp conjugates and rational Fourier spanning (DUB-17/18)"] --> GAMMAONEINTEGRAL8522\n  GAMMAONEINTEGRAL8522["Actual integral Fourier spanning and coefficient-field-valued cusp to regular differential realization proved. Converse, Picard/H1/diamond, original all-weight association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
s=re.sub(r'^edge = .+$',lambda _:'edge = '+repr(oldedge),s,flags=re.M)
s=re.sub(r'^arch.write_text\(.*$',lambda _:"arch.write_text(arch.read_text(encoding='utf-8').replace(edge,"+repr(newedge)+"),encoding='utf-8')",s,flags=re.M)
s=re.sub(r'^    "promotionChanges": .+$',lambda _:'    "promotionChanges": '+repr('Only scratch imports are qualified. All final audited statements, proof bodies and comments remain identical. Original Fricke and integral-ratio fields, exact Laurent and Fourier coefficients, integer denominators, actual cusp forms and actual regular differentials are retained. No source contract is weakened.')+',',s,flags=re.M)
a=s.index("b = re.sub('  logInfo"); b=s.index(', b)',a)+len(', b)')
logline='  logInfo m!"SOURCE GAMMA ONE INTEGRAL DIFFERENTIAL AUDIT PASS: {count} theorems including private/generated declarations. Actual integral Fourier spanning and forward regular differential realization are proved. Converse and arithmetic comparison remain; 16/20 gates."\n'
s=s[:a]+'b = re.sub('+repr('  logInfo m!".*"\n')+', '+repr(logline)+', b)'+s[b:]
output('integrate_source_gamma_one_integral_differential_8522.py', s)
scripts=['integrate_source_gamma_one_integral_differential_8522.py']
for stem in ['prepare_gamma_one_rational_fourier_production_ownership','prepare_gamma_one_rational_fourier_global_ownership']:
    n=tr(stem+'_8493.py'); output(n,tr((p/(stem+'_8493.py')).read_text(encoding='utf-8'))); scripts.append(n)
s=tr((p/'compare_gamma_one_rational_fourier_ownership_8493b.py').read_text(encoding='utf-8'))
s=s.replace('len(names)==len(certs)==3','len(names)==len(certs)==2').replace('len(allmods)==len(set(allmods))==22','len(allmods)==len(set(allmods))==29')
s=s.replace("result['scratchSum']==89", "result['scratchSum']==91").replace('All 22 mathematical','All 29 mathematical')
n='compare_gamma_one_integral_differential_ownership_8522.py'; output(n,s); scripts.append(n)
s=tr((p/'record_source_gamma_one_rational_fourier_8493.py').read_text(encoding='utf-8'))
s=re.sub(r'\b89\b','91',s).replace('== 22','== 29').replace('"incrementModules": 22','"incrementModules": 29').replace('"linterScopes": 22','"linterScopes": 29').replace('== 3','== 2')
s=s.replace('Three declaration-value audits verify 87 required dependencies.','Two declaration-value audits verify 87 required dependencies.').replace('int(a[2]) == 24587','int(a[2]) == 24650')
n='record_source_gamma_one_integral_differential_8522.py'; output(n,s); scripts.append(n)
s=tr((p/'verify_gamma_one_rational_fourier_8493b.ps1').read_text(encoding='utf-8'))
s=s.replace('compare_gamma_one_integral_differential_ownership_8522b.py','compare_gamma_one_integral_differential_ownership_8522.py')
n='verify_gamma_one_integral_differential_8522.ps1'; output(n,s); scripts.append(n)
s=tr((p/'build_gamma_one_rational_fourier_8493.ps1').read_text(encoding='utf-8'))
s=s.replace(",'prepare_gamma_one_integral_differential_scratch_ownership_8522.py'",'')
a=s.index('$env:LEAN_PATH=$taskScratch'); b=s.index('Remove-Item Env:LEAN_PATH',a)
s=s[:a]+'# Reuse the already passed immutable scratch ownership logs; verification checks them.\n'+s[b:]
n='build_gamma_one_integral_differential_8522.ps1'; output(n,s); scripts.append(n)
n='archive_gamma_one_integral_differential_canonical_8522.py'
output(n,tr((p/'archive_gamma_one_rational_fourier_canonical_8493.py').read_text(encoding='utf-8'))); scripts.append(n)
output('source-gamma-one-integral-differential-scratch-ownership-8522.json',json.dumps([
    'SourceGammaOneIntegralCuspScratchOwnership696V2','SourceGammaOneCuspDifferentialScratchOwnership697'],indent=2)+'\n')
for n in scripts:
    if (p/n).suffix=='.py': ast.parse((p/n).read_text(encoding='utf-8'))
output('gamma-one-integral-differential-preexecution-review-8522.json',json.dumps(dict(
    status='Prepared; require 8493 canonical PASS and archive before integration.',route=routefile,
    routeSha256=sha(p/routefile),modules=29,queries=68,theorems=63,constructions=5,
    exhaustiveScratchChecks=91,proofValueEdges=87,scopes=2,receipts=digests,
    expectedConsumers=24650,expectedConstructions=2445,
    fullGoal='16/20; DUB-17--20 OPEN; all 20 gates unchanged.',
    scripts=[dict(path=str(p/n),sha256=sha(p/n)) for n in scripts],productionMutation=False),indent=2)+'\n')
print(json.dumps(dict(scripts=len(scripts),modules=29,checks=91,productionMutation=False)))
