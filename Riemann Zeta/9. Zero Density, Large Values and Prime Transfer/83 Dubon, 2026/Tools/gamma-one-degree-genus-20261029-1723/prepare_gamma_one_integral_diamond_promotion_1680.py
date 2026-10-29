from pathlib import Path
from datetime import datetime, timezone
import ast, hashlib, json, re
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
stems=['source-even-weight-fricke-trace-1','source-even-weight-fricke-uniform-1',
       'source-even-weight-full-slash-1','source-even-weight-integral-diamond-1']
names=[s+'-scratch-receipt.json' for s in stems]
certs=[json.loads((p/n).read_text(encoding='utf-8')) for n in names]
nm,nq,nt,nd=[sum(len(c[k]) for c in certs) for k in
             ['modules','queries','theoremRegistrations','constructionRegistrations']]
count=sum(c['exhaustiveTheorems'] for c in certs)
edges=sum(c['requiredProofValueEdges'] for c in certs)
assert (nm,nq,nt,nd,count,edges)==(24,70,61,9,93,121)
assert len(json.loads((r/'Tools/scaffold.json').read_text(encoding='utf-8'))['productionModules'])==9270
assert (r/'Tools/gamma-one-peaked-auxiliary-20261028-1626/canonical-evidence-9270.json').exists()
digests={n:sha(p/n) for n in names}
for c in certs:
 assert c['exit']==c['diagnostics']==0
 for row in c['files']:assert sha(Path(row['path']))==row['sha256']

dependency='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> automorphy -> original all-weight characteristic-zero association -> actual finite homogeneous Gamma1 Hecke-character realization -> original degree/genus preservation -> signed-index lower bound -> reduced field action -> integral diamond forms -> uniform level-power slash integrality -> actual even-weight Fricke trace.'
discharged='The actual conjugate-subgroup trace consumes the constructed peaked auxiliary and proves Fricke coefficient integrality. Finite algebraic coefficient descent, the existing integral cusp basis and discriminant cancellation prove a common denominator, then arithmetic removes every prime away from the level. This gives uniform level-power Fricke integrality for every nonzero level and every even integer weight. The actual cusp chart at the squared level transfers Fricke to the S move; integral root-of-unity phases supply all integer T moves. Native SL2(Z) generation proves uniform level-power integrality for every slash matrix. Rational cusp diamond expansions and discriminant cancellation prove rationality of the actual transformed modular-form coefficients. Combining rationality and integrality constructs an actual Gamma1 modular form with integer Fourier series equal to a level power times the Gamma0 diamond transform. No auxiliary-existence, common-denominator, transformed-rationality or transformed-integrality premise remains in this final construction.'
boundary='The action on all reduced rational relations, its field and composition laws, the signed-index lower bound and original degree/genus preservation remain open in the production scope. The integral parabolic-preimage theorem remains open; full-H1 surjectivity does not replace it. The arithmetic transfer still retains 3<p and the fixed exceptional-prime exclusion. The required two-dimensional characteristic-zero realization, exceptional coefficient primes, original all-weight association, remaining local/image/regularity inputs, automorphy and literal higher continuation remain required. Acceptance stays 16/20; DUB-17--20 OPEN; every original acceptance test is unchanged.'
route='The fresh reuse search uses anthropics/fermats-last-theorem at pinned commit 6e837e75355538c7f80bab5b956861e86c4eacc2 as inert Apache-2.0 proof references, with exact local source hashes. Native proved cusp bases avoid a separate rational modular-form basis, actual discriminant cancellation handles all even integer weights, and native SL2 generators avoid a new group presentation. Original integral ratios already admit even-weight representatives, so the odd-weight branch is deferred. Four independently audited scopes are promoted with import qualification only; every statement, proof body and comment is preserved. Public/private/generated axiom checks, sixteen linters per module, 121 declaration-value dependency checks, exact theorem ownership and sequential foundation/paper verification remain mandatory. Frozen paper, root pins and owner-only BAT remain unchanged.'
status='The 24-module scratch scope passes 70 public axiom queries, 93 exhaustive theorem checks, sixteen linters per module and four declaration-value audits with 121 required dependency checks, with zero diagnostics. Production aggregate, focused audits and sequential foundation/paper verification of the 9,294-module scope are pending.'
report='Dubon Uniform Slash and Integral Diamond Assessment 2026-10-29.md'
routefile='gamma-one-integral-diamond-promotion-route-1680.json'
def output(n,t):
 f=p/n;assert not f.exists(),f;f.write_text(t,encoding='utf-8')
output(report,'# Uniform slash integrality and actual integral diamond forms — 29 October 2026\n\n'+discharged+'\n\n'+status+'\n\nThe exact source dependency is '+dependency+'.\n\n'+boundary+'\n\n'+route+'\n\nThe final integral diamond theorem consumes the original actual modular form and its integer Fourier series. Its output supplies the witnesses required by the still-unassembled reduced field action. Neither degree/genus preservation nor an additional Dubon acceptance gate is claimed complete.\n')
output(routefile,json.dumps(dict(recordedUTC=datetime.now(timezone.utc).isoformat(),dependency=dependency,discharged=discharged,remaining=boundary,route=route,receipts=digests,modules=nm,queries=nq,exhaustiveScratchChecks=count,proofValueChecks=edges,scopes=4,productionMutation=False),indent=2)+'\n')
subs={'GammaOnePeakedAuxiliary':'GammaOneIntegralDiamond','GammaOneHeckeSeparation':'GammaOnePeakedAuxiliary',
 'gamma_one_peaked_auxiliary':'gamma_one_integral_diamond','gamma_one_hecke_separation':'gamma_one_peaked_auxiliary',
 'gamma-one-peaked-auxiliary':'gamma-one-integral-diamond','gamma-one-hecke-separation':'gamma-one-peaked-auxiliary',
 '9270':'9294','9184':'9270','9,270':'9,294','9,184':'9,270',
 '20261028-1626':'20261029-1680','20261028-1505':'20261028-1626',
 'Original Gamma One even-weight trace and actual peaked auxiliary':'Original Gamma One uniform slash and integral diamond forms',
 'original Gamma One even-weight trace and actual peaked auxiliary':'original Gamma One uniform slash and integral diamond forms',
 'GAMMA ONE PEAKED AUXILIARY':'GAMMA ONE INTEGRAL DIAMOND'}
pat=re.compile('|'.join(re.escape(x) for x in sorted(subs,key=len,reverse=True)))
tr=lambda t:pat.sub(lambda m:subs[m[0]],t)
t=tr((p/'integrate_source_gamma_one_peaked_auxiliary_9270.py').read_text(encoding='utf-8'))
t=re.sub(r'^digests = .+$',lambda _:'digests = '+repr(digests),t,flags=re.M)
t=t.replace('(86, 86, 383, 325, 58)',repr((nm,nm,nq,nt,nd))).replace('assert count == 786','assert count == 93')
t=t.replace('"increment": 86, "queries": 383','"increment": 24, "queries": 70')
for key,val in [('dependency',dependency),('discharged',discharged),('boundary',boundary),('route',route),('status',status)]:
 t=re.sub(r'^'+key+r' = .+$',lambda _,key=key,val=val:key+' = '+repr(val),t,flags=re.M)
evidence=names+[s+'-audit-config.json' for s in stems]+[routefile]
owners=[Path(c['ownershipLog']).with_suffix('').relative_to(p).as_posix() for c in certs]
individualReports=[]
for c in certs:
 for key in ['log','dependencyAuditLog','ownershipLog']:
  f=Path(c[key]);evidence += [f.with_suffix(e).relative_to(p).as_posix() for e in ['.lean','.log','.exit']]
 for row in c['files']:evidence += [Path(row[k]).relative_to(p).as_posix() for k in ['path','compileLog','compileExit']]
 rv=Path(c['reuseReview']);evidence.append(rv.relative_to(p).as_posix())
 routepath=Path(json.loads(rv.read_text(encoding='utf-8'))['routeAssessment']['path']);evidence.append(routepath.relative_to(p).as_posix())
 for row in json.loads(routepath.read_text(encoding='utf-8'))['reuseChecked']:
  f=Path(row['path'])
  if f.is_relative_to(p):evidence.append(f.relative_to(p).as_posix())
  if f.suffix=='.md':individualReports.append(f.name)
individualReports=list(dict.fromkeys(individualReports))
assert len(individualReports)==4
allmods=[m for c in certs for m in c['modules']]
for f in p.iterdir():
 if not f.is_file():continue
 canonical=any(f.name.startswith(m+'.') or f.name.startswith(m+'-') or re.fullmatch(re.escape(m)+r'[0-9]{4}[a-z]?\.(?:lean(?:\.txt)?|log|exit)',f.name) for m in allmods)
 num=re.search(r'([0-9]{4})[a-z]?(?:\.lean(?:\.txt)?|\.[a-z0-9]+)$',f.name)
 numbered=num and 1630<=int(num[1])<=1669
 if (canonical or numbered) and f.suffix in ['.py','.ps1','.json','.lean','.txt','.log','.exit','.md']:evidence.append(f.name)
for folder in p.iterdir():
 if folder.is_dir() and folder.name.startswith('anthropic-'):
  hit=re.search(r'-([0-9]{4})$',folder.name)
  if hit and 1630<=int(hit[1])<=1669:evidence += [f.relative_to(p).as_posix() for f in folder.rglob('*') if f.is_file()]
for n in evidence:assert (p/n).exists(),n
a=t.index('evidence=[p/');b=t.index('for cert in certs:\n    evidence.append',a)
t=t[:a]+'evidence=[p/n for n in '+repr(sorted(set(evidence)))+']\n'+t[b:]
t=t.replace('gamma-one-integral-diamond-promotion-route-1626.json',routefile)
t=t.replace("p / 'Dubon Even Weight Trace and Actual Peaked Auxiliary Assessment 2026-10-28.md'",'p / '+repr(report))
t=re.sub(r"assert sha\(reportSource\) == '[A-F0-9]+'",lambda _:'assert sha(reportSource) == '+repr(sha(p/report)),t)
a=t.index("for name in ['Dubon Even Weight Integral Trace");b=t.index('audit = r /',a)
t=t[:a]+"for name in "+repr(individualReports)+":\n    target=r/name\n    assert not target.exists(),target\n    refresh_pending.append((target,(p/name).read_bytes(),'root'))\n\n"+t[b:]
oldedge=next(x for x in (r/'Dubon Architecture.md').read_text(encoding='utf-8').splitlines() if x.startswith('  GAMMAPEAKED9270['))
newedge='  GAMMAPEAKED9270["Actual even-weight trace and peaked auxiliary with integral expansions and separated cusp decay proved (DUB-17/18)"] --> GAMMAINTEGRAL9294\n  GAMMAINTEGRAL9294["Actual trace application, uniform even-weight SL2 slash integrality and integral Gamma0 diamond forms proved. Reduced field action, signed-index lower bound, degree/genus and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
t=re.sub(r'^edge = .+$',lambda _:'edge = '+repr(oldedge),t,flags=re.M)
t=re.sub(r'^arch.write_text\(.*$',lambda _:"arch.write_text(arch.read_text(encoding='utf-8').replace(edge,"+repr(newedge)+"),encoding='utf-8')",t,flags=re.M)
a=t.index("b = re.sub('  logInfo");b=t.index(', b)',a)+len(', b)')
line='  logInfo m!"SOURCE GAMMA ONE INTEGRAL DIAMOND AUDIT PASS: {count} theorems including private/generated declarations. Actual uniform even-weight slash integrality and integral diamond forms. Reduced field action, degree/genus and source gates OPEN;16/20 gates."\n'
t=t[:a]+'b = re.sub('+repr('  logInfo m!".*"\n')+', '+repr(line)+', b)'+t[b:]
scripts=[]
def script(n,s):
 if n.endswith('.py'):ast.parse(s)
 output(n,s);scripts.append(n)
script('integrate_source_gamma_one_integral_diamond_9294.py',t)
for n in ['prepare_gamma_one_peaked_auxiliary_production_ownership_9270.py','prepare_gamma_one_peaked_auxiliary_global_ownership_9270.py']:
 script(tr(n),tr((p/n).read_text(encoding='utf-8')))
t=tr((p/'compare_gamma_one_peaked_auxiliary_ownership_9270.py').read_text(encoding='utf-8'))
t=t.replace('len(names)==len(certs)==7','len(names)==len(certs)==4').replace('len(set(allmods))==86','len(set(allmods))==24').replace("result['scratchSum']==786","result['scratchSum']==93").replace('All 86 mathematical','All 24 mathematical')
script('compare_gamma_one_integral_diamond_ownership_9294.py',t)
t=tr((p/'record_source_gamma_one_peaked_auxiliary_9270b.py').read_text(encoding='utf-8'))
t=re.sub(r'\b786\b','93',t);t=re.sub(r'\b86\b','24',t)
t=t.replace('len(ownershipComparison["scopes"]) == 7','len(ownershipComparison["scopes"]) == 4')
t=t.replace('Seven declaration-value audits verify 444','Four declaration-value audits verify 121').replace('int(a[2]) == 27085','int(a[2]) == 27146')
t=t.replace('Dubon Even Weight Trace and Actual Peaked Auxiliary Assessment 2026-10-28.md',report)
script('record_source_gamma_one_integral_diamond_9294.py',t)
for prefix in ['build','verify']:
 t=tr((p/(prefix+'_gamma_one_peaked_auxiliary_9270b.ps1')).read_text(encoding='utf-8')).replace('9294b.ps1','9294.ps1').replace('9294b.py','9294.py')
 script(prefix+'_gamma_one_integral_diamond_9294.ps1',t)
t=tr((p/'archive_gamma_one_peaked_auxiliary_canonical_9270.py').read_text(encoding='utf-8'))
t=t.replace('original Gamma One even-weight trace, exact Siegel expansions and constructed actual peaked auxiliary','original Gamma One uniform even-weight slash integrality and actual integral diamond forms')
script('archive_gamma_one_integral_diamond_canonical_9294.py',t)
t=tr((p/'preflight_gamma_one_peaked_auxiliary_9270.py').read_text(encoding='utf-8'))
t=t.replace("==86 and len(ns['queries'])==383 and ns['count']==786","==24 and len(ns['queries'])==70 and ns['count']==93").replace('modules=86,queries=383,exhaustiveScratchChecks=786,proofValueChecks=444','modules=24,queries=70,exhaustiveScratchChecks=93,proofValueChecks=121')
script('preflight_gamma_one_integral_diamond_9294.py',t)
output('source-gamma-one-integral-diamond-scratch-ownership-9294.json',json.dumps(owners,indent=2)+'\n')
output('gamma-one-integral-diamond-preexecution-review-9294.json',json.dumps(dict(status='Prepared only; predecessor9270 canonical PASS and archived evidence required. Integral diamond witnesses are constructed; reduced field action and source gates remain required.',modules=nm,queries=nq,theorems=nt,constructions=nd,exhaustiveScratchChecks=count,proofValueChecks=edges,scopes=4,receipts=digests,expectedConsumers=27146,expectedConstructions=2948,fullGoal=boundary,scripts=[dict(path=str(p/n),sha256=sha(p/n)) for n in scripts],productionMutation=False),indent=2)+'\n')
print(json.dumps(dict(scripts=len(scripts),modules=nm,checks=count,proofEdges=edges,productionMutation=False)))
