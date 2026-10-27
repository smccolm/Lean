from pathlib import Path
import ast,json,re,hashlib
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
names=['source-gamma-one-period-germ-1-scratch-receipt.json', 'source-gamma-one-analytic-residues-3-scratch-receipt.json', 'source-gamma-one-unramified-charts-2-scratch-receipt.json']
certs=[json.loads((p/n).read_text(encoding='utf-8')) for n in names]
digests={n:sha(p/n) for n in names}
assert tuple(sum(len(c[k]) for c in certs) for k in ['modules','queries','theoremRegistrations','constructionRegistrations'])==(6,19,18,1)
assert sum(c['exhaustiveTheorems'] for c in certs)==31
assert sum(c['requiredProofValueEdges'] for c in certs)==43
routefile='gamma-one-period-charts-promotion-route-709.json'
archive='Tools/gamma-one-period-charts-20261026-709'
dependency='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> arithmetic realization of original finite Gamma1 Hecke characters -> Picard/H1, full/parabolic, transpose and diamond comparison retaining the original homogeneous coefficient endomorphism -> actual differential/cusp period normalization and original analytic place charts.'
discharged='The actual Fourier-normalized regular-differential/cusp equivalence has the exact analytic integrand 2*pi*i times the cusp form, for every original regular differential including zero. Actual residue evaluation on the original Gamma field equals the regular analytic limit and the meromorphic normal form, with exact normalized-place orders and punctured-germ equality. At each unramified analytic center, one radius and the actual uniformizer construct an injective local chart with normalized orders for every original field element. Exact j-multiplicity and isolated E4/E6 zeros derive unramifiedness away from those zeros; no chart, residue comparison, order model or differential-coordinate witness is supplied.'
boundary='Elliptic-center ramified descent, finite/cusp place exhaustion and global Gamma1 charts remain, followed by actual global period and Hecke/diamond/Picard/H1 comparison. These local charts do not close the full arithmetic realization of original finite homogeneous-coefficient characters. Coefficient-field transport, Frobenius/inertia, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain. The full all-weight arithmetic goal is unchanged. Complex semisimplicity, finite characters, Witt coefficients and universal deformation rings do not supply a characteristic-zero lift or point. 16/20; DUB-17--20 OPEN.'
route='Reuse the proved Fourier equivalence and quotient normalization to identify the analytic integrand. Reuse generic rational residue evaluation, finite-coordinate closed residue fields and native meromorphic normal form. Reuse the exact j-multiplicity theorem and generic inverse-function parameter theorem for actual unramified charts. Selected pinned FLT ramification files are archived for route assessment; they do not supply a locally certified import closure. Only audited mathematical sources are promoted and only imports are qualified. Failed variants and audit/helper evidence remain preserved. Pins, proof limits, frozen paper and all twenty acceptance gates are unchanged.'
status='The exact actual differential integrand, algebraic/analytic residue comparison and unramified charts pass 31 exhaustive scratch theorem checks and 19 public axiom queries across 6 modules, with sixteen linters per module and zero diagnostics. Three declaration-value audits verify 43 required dependencies. Production aggregate, focused audit and sequential foundation/paper verification of the 8,554-module scope are pending.'
def output(n,s):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(s)
output(routefile,json.dumps(dict(scope=709,scopeIds=['705','706','707'],receipts=digests,dependency=dependency,discharged=discharged,remaining=boundary,route=route,precedingCanonicalScope=8548,rootPinsChanged=False,proofLimitsChanged=False,externalImport=False,fullGoal='16/20; DUB-17--20 OPEN; all 20 gates unchanged.',reason='Require preceding canonical PASS and immutable archive before production mutation.'),indent=2)+'\n')
repl={'gamma-one-integral-differential-promotion-route-699.json': 'gamma-one-period-charts-promotion-route-709.json', 'Tools/gamma-one-integral-differential-20261026-699': 'Tools/gamma-one-period-charts-20261026-709', 'Tools/gamma-one-rational-fourier-20261026-692': 'Tools/gamma-one-regular-cusp-20261026-704', 'appliedSourceGammaOneIntegralDifferential': 'appliedSourceGammaOnePeriodCharts', 'appliedSourceGammaOneRationalFourier': 'appliedSourceGammaOneRegularCusp', 'SourceGammaOneIntegralDifferential': 'SourceGammaOnePeriodCharts', 'gamma_one_integral_differential': 'gamma_one_period_charts', 'source-gamma-one-integral-differential': 'source-gamma-one-period-charts', 'SOURCE GAMMA ONE INTEGRAL DIFFERENTIAL': 'SOURCE GAMMA ONE PERIOD CHARTS', 'actual Gamma1 integral Fourier spanning and differential realization': 'actual Gamma1 period normalization and local charts', 'Actual Gamma1 integral Fourier spanning and differential realization': 'Actual Gamma1 period normalization and local charts', '8,522': '8,554', '8,493': '8,548', '8522': '8554', '8493': '8548'}
rx=re.compile('|'.join(map(re.escape,sorted(repl,key=len,reverse=True))))
tr=lambda s:rx.sub(lambda m:repl[m[0]],s)
s=tr((p/'integrate_source_gamma_one_integral_differential_8522.py').read_text(encoding='utf-8'))
s=re.sub(r'^digests = .+$',lambda _:'digests = '+repr(digests),s,flags=re.M)
s=s.replace('(29, 29, 68, 63, 5)','(6, 6, 19, 18, 1)').replace('count == 91','count == 31').replace('"increment": 29, "queries": 68','"increment": 6, "queries": 19')
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
 if f.is_file() and f.suffix in ['.json','.py','.ps1','.txt','.log','.exit'] and re.search(r'(?<!\d)(705|706|707|708)[a-z]?(?:\.|-)',f.name):evidence.append(f.name)
evidence += [n.replace('-scratch-receipt.json','-audit-config.json') for n in names]
owners=['SourceGammaOnePeriodGermScratchOwnership705', 'SourceGammaOneAnalyticResiduesScratchOwnership706', 'SourceGammaOneUnramifiedChartsScratchOwnership707']
for stem in owners:evidence += [stem+ext for ext in ['.lean','.log','.exit']]
folders=['gamma-one-ramification-core-reuse-708']+[f.name for f in p.iterdir() if f.is_dir() and re.search(r'(705|706|707|708)[a-z]?$',f.name)]
assert len(folders)==7,folders
for n in evidence+folders:assert (p/n).exists(),n
s=s[:a]+'evidence=[p/'+repr(routefile)+']\nevidence += [p/n for n in '+repr(sorted(set(evidence)))+']\nfor folder in '+repr(folders)+':\n    evidence += sorted(f for f in (p/folder).rglob("*") if f.is_file())\n'+s[b:]
oldedge='  GAMMAONEREGULAR8548["Actual complex Gamma1 regular-differential/cusp linear equivalence with exact Fourier normalization proved. Original Hecke/diamond/Picard/H1, all-weight arithmetic association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
newedge='  GAMMAONEREGULAR8548["Actual complex Gamma1 regular-differential/cusp equivalence with exact Fourier normalization (DUB-17/18)"] --> GAMMAONEPERIOD8554\n  GAMMAONEPERIOD8554["Exact differential integrand, actual residue comparison and unramified local charts proved. Elliptic/global charts, period/Hecke/diamond/Picard/H1, all-weight arithmetic association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
assert (r/'Dubon Architecture.md').read_text(encoding='utf-8').count(oldedge)==1
s=re.sub(r'^edge = .+$',lambda _:'edge = '+repr(oldedge),s,flags=re.M)
s=re.sub(r'^arch.write_text\(.*$',lambda _:"arch.write_text(arch.read_text(encoding='utf-8').replace(edge,"+repr(newedge)+"),encoding='utf-8')",s,flags=re.M)
s=re.sub(r'^    "promotionChanges": .+$',lambda _:'    "promotionChanges": '+repr('Only scratch imports are qualified. All final audited statements, proof bodies and comments remain identical. The original function field, actual regular differentials, native cusp forms, literal Fourier series and exact complex normalization are retained. No source contract is weakened.')+',',s,flags=re.M)
a=s.index("b = re.sub('  logInfo");b=s.index(', b)',a)+len(', b)')
logline='  logInfo m!"SOURCE GAMMA ONE PERIOD CHARTS AUDIT PASS: {count} theorems including private/generated declarations. The exact actual Gamma1 differential integrand, residue comparison and unramified charts are proved. Elliptic and global chart/period obligations remain. Original Hecke/diamond/Picard/H1 arithmetic comparison remains; 16/20 gates."\n'
s=s[:a]+'b = re.sub('+repr('  logInfo m!".*"\n')+', '+repr(logline)+', b)'+s[b:]
output('integrate_source_gamma_one_period_charts_8554.py',s)
scripts=['integrate_source_gamma_one_period_charts_8554.py']
for stem in ['prepare_gamma_one_integral_differential_production_ownership','prepare_gamma_one_integral_differential_global_ownership']:
 n=tr(stem+'_8522.py');output(n,tr((p/(stem+'_8522.py')).read_text(encoding='utf-8')));scripts.append(n)
s=tr((p/'compare_gamma_one_integral_differential_ownership_8522.py').read_text(encoding='utf-8'))
s=s.replace('len(names)==len(certs)==2','len(names)==len(certs)==3').replace('len(allmods)==len(set(allmods))==29','len(allmods)==len(set(allmods))==6').replace("result['scratchSum']==91","result['scratchSum']==31").replace('All 29 mathematical','All 6 mathematical')
n='compare_gamma_one_period_charts_ownership_8554.py';output(n,s);scripts.append(n)
s=tr((p/'record_source_gamma_one_integral_differential_8522.py').read_text(encoding='utf-8'))
s=re.sub(r'\b91\b','31',s);s=re.sub(r'== 29\b','== 6',s);s=re.sub(r'== 2\b','== 3',s)
s=s.replace('"incrementModules": 29','"incrementModules": 6').replace('"linterScopes": 29','"linterScopes": 6').replace('Two declaration-value audits verify 87 required dependencies.','Three declaration-value audits verify 43 required dependencies.').replace('int(a[2]) == 24650','int(a[2]) == 24737')
n='record_source_gamma_one_period_charts_8554.py';output(n,s);scripts.append(n)
for stem in ['verify_gamma_one_integral_differential','build_gamma_one_integral_differential']:
 n=tr(stem+'_8522.ps1');output(n,tr((p/(stem+'_8522.ps1')).read_text(encoding='utf-8')));scripts.append(n)
n='archive_gamma_one_period_charts_canonical_8554.py';output(n,tr((p/'archive_gamma_one_integral_differential_canonical_8522.py').read_text(encoding='utf-8')));scripts.append(n)
output('source-gamma-one-period-charts-scratch-ownership-8554.json',json.dumps(owners,indent=2)+'\n')
for n in scripts:
 if (p/n).suffix=='.py':ast.parse((p/n).read_text(encoding='utf-8'))
output('gamma-one-period-charts-preexecution-review-8554.json',json.dumps(dict(status='Prepared; require 8548 canonical PASS and archive before integration.',route=routefile,routeSha256=sha(p/routefile),modules=6,queries=19,theorems=18,constructions=1,exhaustiveScratchChecks=31,proofValueEdges=43,scopes=3,receipts=digests,expectedConsumers=24737,expectedConstructions=2457,fullGoal='16/20; DUB-17--20 OPEN; all 20 gates unchanged.',scripts=[dict(path=str(p/n),sha256=sha(p/n)) for n in scripts],productionMutation=False),indent=2)+'\n')
print(json.dumps(dict(scripts=len(scripts),modules=6,checks=31,archivedFailureAndReuseFolders=len(folders),productionMutation=False)))