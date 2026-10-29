from pathlib import Path
from datetime import datetime,timezone
import ast,hashlib,json,re
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
stems=['source-gamma-one-diamond-quotient-1','source-gamma-one-diamond-transfer-1']
names=[s+'-scratch-receipt.json' for s in stems]
certs=[json.loads((p/n).read_text(encoding='utf-8')) for n in names]
assert tuple(sum(len(c[k]) for c in certs) for k in ['modules','queries','theoremRegistrations','constructionRegistrations'])==(12,27,22,5)
total=sum(c['exhaustiveTheorems'] for c in certs);assert total==100
edges=sum(c['requiredProofValueEdges'] for c in certs);assert edges==51
digests={n:sha(p/n) for n in names}
for c in certs:
 assert c['exit']==c['diagnostics']==0
 for row in c['files']:assert sha(Path(row['path']))==row['sha256']
dependency='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> automorphy -> original all-weight characteristic-zero association -> finite original Hecke-character realization -> diamond-one quotient of the actual homogeneous Tate dual and its original parabolic transfer.'
discharged='The original norm-derived Frobenius identity now retains the actual combined coefficient/Picard diamond on every homogeneous Tate-dual class. The quotient by all original diamond-minus-one relations has a genuine finite continuous Galois action. Projecting the polynomial removes its diamond term; invertibility of the quotient Galois action then derives stability under the actual original good-prime Hecke operator. The descended operator satisfies its Frobenius polynomial on the entire quotient. The original Tate/parabolic-H1 equivalence and native diamond-invariant transfer give a map from this quotient to the original coefficient H1. An assembled consumer derives the Hecke square for the geometrically constructed operator, without a supplied operator descent. Under the separately identified original integral parabolic-transfer input, the original primitive form character proves this quotient nonzero away from its fixed exceptional integer. This nonvanishing deduction assumes no eigensystem or nonzero vector and requires no geometric degree/genus equality.'
boundary='Actual original coordinate-degree and genus preservation remain open and explicit in the Frobenius/Hecke construction. The original integral parabolic-preimage theorem remains unproved; full-H1 surjectivity is not substituted for it. The transfer comparison retains 3<p, and nonvanishing also retains the original exceptional-prime exclusion. A character on the actual quotient operator algebra, its required two-dimensional realization, exceptional coefficient primes, original all-weight characteristic-zero association, remaining local/image/regularity inputs, automorphy and literal higher continuation remain required. Acceptance stays 16/20; DUB-17--20 OPEN; all twenty acceptance tests are unchanged.'
route='The October 28 upstream refresh and native reuse search were checked before expansion. The exact original Picard/Tate norm identity, homogeneous coefficient square, cyclotomic Frobenius value, Galois/diamond commutation, finite Tate-dual continuity, native quotient representation, Tate/H1 and Hecke comparisons, diamond-invariant transfer and original parabolic congruence theorem are reused. The quotient polynomial itself gives Hecke stability, avoiding a separate Hecke/diamond commutation development. Native ideal-power containment and maximality supply nonvanishing. Narrow map lemmas and cached carrier structures resolve elaboration costs without raising proof limits. The new arithmetic-diamond-polynomial module preserves the existing arithmetic-diamond field module. All promoted mathematical bodies and comments remain identical to their audited forms after import qualification; frozen sources, root pins and owner-only BAT are unchanged.'
status='The twelve-module scope passes 27 public axiom queries, 100 exhaustive scratch theorem checks, sixteen linters per module and two declaration-value audits with 51 required dependency checks, with zero diagnostics. Production aggregate, focused audits and sequential foundation/paper verification of the 9,161-module scope are pending.'
report='Dubon Original Gamma One Diamond Quotient Assessment 2026-10-28.md'
rf=p/report
old='All twelve versioned scratch modules compile with zero diagnostics. Canonical scratch import normalization, exhaustive public/private/generated theorem checks, sixteen linters per module, declaration-value dependency audits and exact ownership recording are pending. No production promotion or assembled PASS is claimed for this scope.'
text=rf.read_text(encoding='utf-8');assert text.count(old)==1
rf.write_text(text.replace(old,status+' No production promotion or assembled PASS is claimed for this scope.'),encoding='utf-8')
routefile='gamma-one-diamond-quotient-promotion-route-1453.json'
def output(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output(routefile,json.dumps(dict(recordedUTC=datetime.now(timezone.utc).isoformat(),dependency=dependency,discharged=discharged,remaining=boundary,route=route,receipts=digests,modules=12,queries=27,exhaustiveScratchChecks=100,proofValueChecks=51,productionMutation=False),indent=2)+'\n')
subs={'GammaOneGlobalGalois':'GammaOneDiamondQuotient','gamma_one_global_galois':'gamma_one_diamond_quotient','gamma-one-global-galois':'gamma-one-diamond-quotient','GammaOneTateFrobenius':'GammaOneGlobalGalois','gamma_one_tate_frobenius':'gamma_one_global_galois','gamma-one-tate-frobenius':'gamma-one-global-galois','9149':'9161','9123':'9149','9,149':'9,161','9,123':'9,149','20261028-1431':'20261028-1453','20261028-1402':'20261028-1431'}
pat=re.compile('|'.join(re.escape(x) for x in sorted(subs,key=len,reverse=True)))
tr=lambda s:pat.sub(lambda m:subs[m[0]],s)
s=tr((p/'integrate_source_gamma_one_global_galois_9149.py').read_text(encoding='utf-8'))
s=re.sub(r'^digests = .+$',lambda _:'digests = '+repr(digests),s,flags=re.M)
s=s.replace('(26, 26, 39, 33, 6)','(12, 12, 27, 22, 5)').replace('assert count == 113','assert count == 100')
s=s.replace('"increment": 26, "queries": 39','"increment": 12, "queries": 27')
for key,val in [('dependency',dependency),('discharged',discharged),('boundary',boundary),('route',route),('status',status)]:
 s=re.sub(r'^'+key+r' = .+$',lambda _,key=key,val=val:key+' = '+repr(val),s,flags=re.M)
s=s.replace('Original Gamma One global Galois realization','Original Gamma One diamond quotient and transfer')
s=s.replace('The original Gamma1 fields, actual homogeneous coefficients, cyclotomic character and Picard Tate action are retained. The local coordinate-degree/genus hypotheses and the parabolic comparison range are explicit; continuity and finite factorization impose no additional geometric hypothesis.','The original Gamma1 fields, actual homogeneous coefficients, Picard Tate action, original good-prime operators and cohomology transfer are retained. Degree/genus hypotheses, original integral parabolic transfer and exceptional-prime conditions remain explicit.')
evidence=names+[n+'-audit-config.json' for n in stems]
owners=[Path(c['ownershipLog']).stem for c in certs]
for c in certs:
 for key in ['log','dependencyAuditLog']:
  f=Path(c[key]);evidence += [f.with_suffix(e).name for e in ['.lean','.log','.exit']]
 for row in c['files']:evidence += [Path(row['path']).name,Path(row['compileLog']).name,Path(row['compileExit']).name]
 evidence.append(Path(c['reuseReview']).name)
 rv=json.loads(Path(c['reuseReview']).read_text(encoding='utf-8'));evidence.append(Path(rv['routeAssessment']['path']).name)
pattern=r'(?<!\d)(?:'+'|'.join(str(i) for i in range(1433,1449))+r')[a-z]?(?!\d)'
for f in p.iterdir():
 if f.is_file() and f.suffix in ['.json','.py','.ps1','.txt','.log','.exit','.lean','.md'] and re.search(pattern,f.name):evidence.append(f.name)
for n in owners:evidence += [n+e for e in ['.lean','.log','.exit']]
for n in evidence:assert (p/n).exists(),n
a=s.index('evidence=[p/');b=s.index('for cert in certs:\n    evidence.append',a)
s=s[:a]+'evidence=[p/'+repr(routefile)+']\nevidence += [p/n for n in '+repr(sorted(set(evidence)))+']\n'+s[b:]
s=s.replace('gamma-one-diamond-quotient-promotion-route-1431.json',routefile)
s=s.replace("p / 'Dubon Original Gamma One Global Galois Assessment 2026-10-28.md'",'p / '+repr(report))
s=re.sub(r"assert sha\(reportSource\) == '[A-F0-9]+'",lambda _:'assert sha(reportSource) == '+repr(sha(rf)),s)
oldedge=next(x for x in (r/'Dubon Architecture.md').read_text(encoding='utf-8').splitlines() if x.startswith('  GAMMAGALOIS9149['))
newedge='  GAMMAGALOIS9149["Actual continuous finite homogeneous Tate Galois action and faithful finite factor; conditional arithmetic descent (DUB-17/18)"] --> GAMMADIAMOND9161\n  GAMMADIAMOND9161["Actual diamond-one quotient, derived Hecke stability and Frobenius polynomial; original transfer and conditional nonvanishing. Degree/genus equality, parabolic transfer, character/two-dimensional realization and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
s=re.sub(r'^edge = .+$',lambda _:'edge = '+repr(oldedge),s,flags=re.M)
s=re.sub(r'^arch.write_text\(.*$',lambda _:"arch.write_text(arch.read_text(encoding='utf-8').replace(edge,"+repr(newedge)+"),encoding='utf-8')",s,flags=re.M)
a=s.index("b = re.sub('  logInfo");b=s.index(', b)',a)+len(', b)')
line='  logInfo m!"SOURCE GAMMA ONE DIAMOND QUOTIENT AUDIT PASS: {count} theorems including private/generated declarations. Actual finite continuous diamond-one quotient, original Hecke stability and Frobenius from degree/genus equality; original transfer and nonvanishing from explicit parabolic input. Character/two-dimensional realization and remaining gates OPEN;16/20 gates."\n'
s=s[:a]+'b = re.sub('+repr('  logInfo m!".*"\n')+', '+repr(line)+', b)'+s[b:]
scripts=[]
def script(n,s):
 if n.endswith('.py'):ast.parse(s)
 output(n,s);scripts.append(n)
script('integrate_source_gamma_one_diamond_quotient_9161.py',s)
for n in ['prepare_gamma_one_global_galois_production_ownership_9149.py','prepare_gamma_one_global_galois_global_ownership_9149.py']:
 script(tr(n),tr((p/n).read_text(encoding='utf-8')))
s=tr((p/'compare_gamma_one_global_galois_ownership_9149.py').read_text(encoding='utf-8'))
s=s.replace("result['scratchSum']==113","result['scratchSum']==100")
script('compare_gamma_one_diamond_quotient_ownership_9161.py',s)
s=tr((p/'record_source_gamma_one_global_galois_9149.py').read_text(encoding='utf-8'))
s=re.sub(r'\b113\b','100',s)
s=s.replace('Three declaration-value audits verify 80','Two declaration-value audits verify 51').replace('int(a[2]) == 26695','int(a[2]) == 26717')
s=s.replace('Dubon Original Gamma One Global Galois Assessment 2026-10-28.md',report)
s=s.replace('GAMMA ONE GLOBAL GALOIS','GAMMA ONE DIAMOND QUOTIENT').replace('original Gamma One global Galois realization','original Gamma One diamond quotient and transfer')
script('record_source_gamma_one_diamond_quotient_9161.py',s)
for prefix in ['build','verify']:
 script(prefix+'_gamma_one_diamond_quotient_9161.ps1',tr((p/(prefix+'_gamma_one_global_galois_9149.ps1')).read_text(encoding='utf-8')))
s=tr((p/'archive_gamma_one_global_galois_canonical_9149.py').read_text(encoding='utf-8'))
s=s.replace('original Gamma One continuous finite homogeneous Tate Galois action, faithful finite factor, conditional prescribed arithmetic descent and parabolic Galois-orbit Frobenius','original Gamma One actual diamond-one quotient, derived original Hecke stability and Frobenius, original transfer and conditional nonvanishing')
script('archive_gamma_one_diamond_quotient_canonical_9161.py',s)
s=tr((p/'preflight_gamma_one_global_galois_9149.py').read_text(encoding='utf-8'))
s=s.replace("==26 and len(ns['queries'])==39 and ns['count']==113","==12 and len(ns['queries'])==27 and ns['count']==100")
s=s.replace('modules=26,queries=39,exhaustiveScratchChecks=113,proofValueChecks=80','modules=12,queries=27,exhaustiveScratchChecks=100,proofValueChecks=51')
script('preflight_gamma_one_diamond_quotient_9161.py',s)
output('source-gamma-one-diamond-quotient-scratch-ownership-9161.json',json.dumps(owners,indent=2)+'\n')
output('gamma-one-diamond-quotient-preexecution-review-9161.json',json.dumps(dict(status='Prepared only. Integration requires predecessor canonical PASS and archive.',modules=12,queries=27,theorems=22,constructions=5,exhaustiveScratchChecks=100,proofValueChecks=51,scopes=2,receipts=digests,expectedConsumers=26717,expectedConstructions=2868,fullGoal=boundary,scripts=[dict(path=str(p/n),sha256=sha(p/n)) for n in scripts],productionMutation=False),indent=2)+'\n')
print(json.dumps(dict(scripts=len(scripts),modules=12,checks=100,proofEdges=51,productionMutation=False)))
