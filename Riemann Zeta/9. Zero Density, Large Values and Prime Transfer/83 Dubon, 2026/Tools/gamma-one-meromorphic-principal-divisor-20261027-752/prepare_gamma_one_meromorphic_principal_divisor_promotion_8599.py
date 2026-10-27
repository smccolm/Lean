from pathlib import Path
import re,json,hashlib,ast
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
stems=['source-gamma-one-cusp-residues-1','source-gamma-one-cusp-exhaustion-1','source-gamma-one-holomorphic-field-1','source-gamma-one-pole-clearing-normalization-1','source-gamma-one-meromorphic-field-1','source-gamma-one-meromorphic-principal-divisor-1']
names=[n+'-scratch-receipt.json' for n in stems]
certs=[json.loads((p/n).read_text(encoding='utf-8')) for n in names]
digests={n:sha(p/n) for n in names}
assert tuple(sum(len(c[k]) for c in certs) for k in ['modules','queries','theoremRegistrations','constructionRegistrations'])==(13,31,31,0)
assert sum(c['exhaustiveTheorems'] for c in certs)==40
assert sum(c['requiredProofValueEdges'] for c in certs)==79
assessment=json.loads((p/'gamma-one-period-reuse-assessment-752/assessment.json').read_text(encoding='utf-8'))
assert sha(p/'gamma-one-period-reuse-assessment-752/assessment.json')=='7504E8D92EA153AE5CF550BBBECD5F0E6F32E81265B4634A6DCB57958D9FED2E'
dependency=assessment['chain']
discharged=('The exact invariant meromorphic-function contract gives a literal principal divisor in the original Gamma1 integral-ratio field. Actual cusp exhaustion follows from existing one-pole functions and weight-zero constancy. Finite-coordinate pole clearing and native meromorphic normalization construct a holomorphic product; discriminant powers control every translated cusp and actual modular-ratio membership returns the original field element. Exact analytic orders and every cusp order are derived. Nonzero translated limits force order zero at all j-pole places. No field-realization, cusp-exhaustion or cusp-order hypothesis is supplied to the final consumer.')
boundary=('Constructing the meromorphic function from the Abel-Jacobi period condition still requires genuine real period surjectivity and reciprocity. Actual global periods and Hecke/diamond/Picard/H1, full/parabolic and transpose comparisons remain. Arithmetic realization of original finite homogeneous-coefficient Gamma1 characters, coefficient-field transport, Frobenius/inertia, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain. Complex semisimplicity, finite characters, Witt coefficients and universal deformation rings do not supply a characteristic-zero lift. 16/20; DUB-17--20 OPEN; all twenty gates unchanged.')
route=('The renewed search is recorded in Dubon Reuse Refresh 2026-10-27.md and Dubon Reuse Route Assessment 2026-10-27.md. Nine further pinned primary proof files were inspected. Existing local pole clearing, actual field membership and cusp functions give a shorter conversion than the candidate inverse-j/full-level-Galois cusp-order argument. The direct Gamma1 genus/Manin route and candidate principal-level period route are compared before expanding either. External import closures are not locally built. Only imports are qualified on promotion; audited statements and proof bodies remain identical. All failures and research snapshots are retained. Root pins, proof limits, source and full all-weight contract are unchanged.')
status=('The thirteen-module original Gamma1 meromorphic principal-divisor conversion passes 31 public axiom queries, 40 exhaustive scratch theorem checks, sixteen linters per module and six declaration-value audits covering 79 required dependencies, with zero diagnostics. Production aggregate, focused audits and sequential foundation/paper verification of the 8,599-module scope are pending.')
routefile='gamma-one-meromorphic-principal-divisor-promotion-route-752.json'
archive='Tools/gamma-one-meromorphic-principal-divisor-20261027-752'
repl={'Tools/gamma-one-finite-charts-divisors-20261027-740':archive,'Tools/gamma-one-analytic-orbits-20261027-730':'Tools/gamma-one-finite-charts-divisors-20261027-740','appliedSourceGammaOneFiniteChartsDivisors':'appliedSourceGammaOneMeromorphicPrincipalDivisor','appliedSourceGammaOneAnalyticOrbits':'appliedSourceGammaOneFiniteChartsDivisors','SourceGammaOneFiniteChartsDivisors':'SourceGammaOneMeromorphicPrincipalDivisor','gamma_one_finite_charts_divisors':'gamma_one_meromorphic_principal_divisor','source-gamma-one-finite-charts-divisors':'source-gamma-one-meromorphic-principal-divisor','gamma-one-finite-charts-divisors-promotion-route-740.json':routefile,'SOURCE GAMMA ONE FINITE CHARTS AND DIVISORS':'SOURCE GAMMA ONE MEROMORPHIC PRINCIPAL DIVISOR','actual Gamma1 finite charts and analytic divisor representatives':'actual Gamma1 meromorphic principal-divisor conversion','Actual Gamma1 finite charts and analytic divisor representatives':'Actual Gamma1 meromorphic principal-divisor conversion','8,586':'8,599','8,576':'8,586','8586':'8599','8576':'8586'}
rx=re.compile('|'.join(map(re.escape,sorted(repl,key=len,reverse=True))))
tr=lambda s:rx.sub(lambda m:repl[m[0]],s)
def output(n,s):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(s)
output(routefile,json.dumps(dict(scope=752,scopeIds=list(range(742,752)),researchScopes=[753,754,755],receipts=digests,dependency=dependency,discharged=discharged,remaining=boundary,route=route,precedingCanonicalScope=8586,rootPinsChanged=False,proofLimitsChanged=False,externalImport=False,fullGoal='16/20; DUB-17--20 OPEN; all twenty gates unchanged.',productionMutation=False),indent=2)+'\n')
s=tr((p/'integrate_source_gamma_one_finite_charts_divisors_8586.py').read_text(encoding='utf-8'))
s=s.replace('paper-verification-8586-console.exit','paper-verification-8586b-console.exit')
s=re.sub(r'^digests = .+$',lambda _:'digests = '+repr(digests),s,flags=re.M)
s=s.replace('(10, 10, 22, 21, 1)','(13, 13, 31, 31, 0)').replace('count == 48','count == 40').replace('"increment": 10, "queries": 22','"increment": 13, "queries": 31')
for k,v in [('dependency',dependency),('discharged',discharged),('boundary',boundary),('route',route),('status',status)]:
 assert re.search(r'^'+k+r' = .+$',s,re.M),k
 s=re.sub(r'^'+k+r' = .+$',lambda _,k=k,v=v:k+' = '+repr(v),s,flags=re.M)
a=s.index('at = at.replace(dm,');b=s.index('research_path = ',a)
s=s[:a]+'assert not defs  # This promotion adds only theorem registrations.\n'+s[b:]
owners=['SourceGammaOneCuspResiduesScratchOwnership742','SourceGammaOneCuspExhaustionScratchOwnership743','SourceGammaOneHolomorphicFieldScratchOwnership744','SourceGammaOnePoleClearingNormalizationScratchOwnership746','SourceGammaOneMeromorphicFieldScratchOwnership749','SourceGammaOneMeromorphicPrincipalDivisorScratchOwnership751']
evidence=list(names)+[n+'-audit-config.json' for n in stems]
for c in certs:
 for k in ['log','dependencyAuditLog']:
  f=Path(c[k]);evidence += [f.with_suffix(e).name for e in ['.lean','.log','.exit']]
 for row in c['files']:
  f=Path(row['path']);evidence += [f.with_suffix(e).name for e in ['.lean','.log','.exit']]
 evidence.append(Path(c['reuseReview']).name)
 review=json.loads(Path(c['reuseReview']).read_text(encoding='utf-8'))
 evidence.append(Path(review['routeAssessment']['path']).name)
pattern=r'(?:742|743|744|745|746|747|748|749|750|751|753|754|755)'
for f in p.iterdir():
 if f.is_file() and ('gamma_one' in f.name or 'gamma-one' in f.name) and f.suffix in ['.json','.py','.ps1','.txt','.log','.exit'] and re.search(r'(?<!\d)'+pattern+r'[a-z]?(?:\.|-)',f.name):evidence.append(f.name)
for n in owners:evidence += [n+e for e in ['.lean','.log','.exit']]
folders=[f.name for f in p.iterdir() if f.is_dir() and f.name.startswith('gamma-one-') and re.search(pattern+r'[a-z]?$',f.name)]
folders.append('gamma-one-period-reuse-assessment-752')
for n in evidence+folders:assert (p/n).exists(),n
a=s.index('evidence=[p/');b=s.index("for cert in certs:\n    evidence.append",a)
s=s[:a]+'evidence=[p/'+repr(routefile)+']\nevidence += [p/n for n in '+repr(sorted(set(evidence)))+']\nfor folder in '+repr(folders)+':\n    evidence += sorted(f for f in (p/folder).rglob("*") if f.is_file())\n'+s[b:]
s=s.replace("if source.suffix=='.lean':target=target.with_name(target.name+'.txt')","if source.suffix in ['.lean','.md']:target=target.with_name(target.name+'.txt')")
s=s.replace("reuse-head-refresh-741/Dubon Reuse Refresh 2026-10-27.md","gamma-one-period-reuse-assessment-752/Dubon Reuse Route Assessment 2026-10-27.md").replace('0492A53D656A52E89B93B5EB506066901BAB9507AF71E81608B394B1A338C34D','5265FE0DF0B08207082C35A1B752D0568235A098823C87BFA9B0433230EB7D72')
oldedge='  GAMMAONEFINITE8586["Exact elliptic ramification, normalized finite charts and analytic representatives of every divisor class proved. Global periods, Hecke/diamond/Picard/H1, all-weight arithmetic association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
newedge='  GAMMAONEFINITE8586["Exact elliptic ramification, normalized finite charts and analytic divisor representatives (DUB-17/18)"] --> GAMMAONEPRINCIPAL8599\n  GAMMAONEPRINCIPAL8599["Original-field meromorphic principal-divisor conversion and every cusp order proved. Function construction from periods, Hecke/diamond/Picard/H1, all-weight arithmetic association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
s=re.sub(r'^edge = .+$',lambda _:'edge = '+repr(oldedge),s,flags=re.M)
s=re.sub(r'^arch.write_text\(.*$',lambda _:"arch.write_text(arch.read_text(encoding='utf-8').replace(edge,"+repr(newedge)+"),encoding='utf-8')",s,flags=re.M)
s=re.sub(r'^    "promotionChanges": .+$',lambda _:'    "promotionChanges": '+repr('Only scratch imports are qualified. All audited statements, proof bodies and comments remain identical. Exact actual field elements, normalized place orders, all nonzero Gamma1 levels and translated cusp limits are retained.')+',',s,flags=re.M)
a=s.index("b = re.sub('  logInfo");b=s.index(', b)',a)+len(', b)')
logline='  logInfo m!"SOURCE GAMMA ONE MEROMORPHIC PRINCIPAL DIVISOR AUDIT PASS: {count} theorems including private/generated declarations. The exact meromorphic function gives a principal divisor in the original Gamma1 field with all cusp orders derived. Its construction from periods and original arithmetic comparison remain; 16/20 gates."\n'
s=s[:a]+'b = re.sub('+repr('  logInfo m!".*"\n')+', '+repr(logline)+', b)'+s[b:]
scripts=[]
def script(n,s):
 if n.endswith('.py'):ast.parse(s)
 output(n,s);scripts.append(n)
script('integrate_source_gamma_one_meromorphic_principal_divisor_8599.py',s)
for stem in ['prepare_gamma_one_finite_charts_divisors_production_ownership','prepare_gamma_one_finite_charts_divisors_global_ownership']:
 n=tr(stem+'_8586.py');script(n,tr((p/(stem+'_8586.py')).read_text(encoding='utf-8')))
s=tr((p/'compare_gamma_one_finite_charts_divisors_ownership_8586.py').read_text(encoding='utf-8'))).replace('len(names)==len(certs)==5','len(names)==len(certs)==6').replace('len(allmods)==len(set(allmods))==10','len(allmods)==len(set(allmods))==13').replace("result['scratchSum']==48","result['scratchSum']==40").replace('All 10 mathematical','All 13 mathematical')
script('compare_gamma_one_meromorphic_principal_divisor_ownership_8599.py',s)
s=tr((p/'record_source_gamma_one_finite_charts_divisors_8586.py').read_text(encoding='utf-8')))
s=re.sub(r'\b48\b','40',s);s=re.sub(r'== 10\b','== 13',s);s=re.sub(r'== 5\b','== 6',s)
s=s.replace('"incrementModules": 10','"incrementModules": 13').replace('"linterScopes": 10','"linterScopes": 13').replace('Five declaration-value audits verify 55 required dependencies.','Six declaration-value audits verify 79 required dependencies.').replace('int(a[2]) == 24813','int(a[2]) == 24844')
script('record_source_gamma_one_meromorphic_principal_divisor_8599.py',s)
for stem in ['build_gamma_one_finite_charts_divisors','verify_gamma_one_finite_charts_divisors']:
 s=tr((p/(stem+'_8586.ps1')).read_text(encoding='utf-8')))
 if stem.startswith('verify'):
  s=s.replace('cmd /c run_lake_build.bat --no-pause *> "$taskRoot.log"',"$ErrorActionPreference='Continue'\ncmd /c run_lake_build.bat --no-pause *> \"$taskRoot.log\"").replace('cmd /c run_dubon_build.bat --no-pause *> "$taskPaperLog.log"',"$ErrorActionPreference='Continue'\ncmd /c run_dubon_build.bat --no-pause *> \"$taskPaperLog.log\"")
  s=s.replace('$taskExit=$LASTEXITCODE\n','$taskExit=$LASTEXITCODE\n$ErrorActionPreference=\'Stop\'\n')
 script(tr(stem+'_8586.ps1'),s)
output('source-gamma-one-meromorphic-principal-divisor-scratch-ownership-8599.json',json.dumps(owners,indent=2)+'\n')
output('gamma-one-meromorphic-principal-divisor-preexecution-review-8599.json',json.dumps(dict(status='Prepared only. Integration requires preceding canonical PASS and archive.',modules=13,queries=31,theorems=31,constructions=0,exhaustiveScratchChecks=40,proofValueEdges=79,scopes=6,receipts=digests,expectedConsumers=24844,expectedConstructions=2465,fullGoal='16/20; DUB-17--20 OPEN; all twenty gates unchanged.',scripts=[dict(path=str(p/n),sha256=sha(p/n)) for n in scripts],productionMutation=False),indent=2)+'\n')
print(json.dumps(dict(scripts=len(scripts),modules=13,checks=40,productionMutation=False)))
