from pathlib import Path
from datetime import datetime,timezone
import ast,hashlib,json,re
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
stems=['source-gamma-one-diamond-quotient-1','source-gamma-one-diamond-transfer-1',
'source-gamma-one-quotient-character-1','source-gamma-one-integral-ratio-1','source-gamma-one-integral-eisenstein-1']
names=[s+'-scratch-receipt.json' for s in stems]
certs=[json.loads((p/n).read_text(encoding='utf-8')) for n in names]
assert tuple(sum(len(c[k]) for c in certs) for k in ['modules','queries','theoremRegistrations','constructionRegistrations'])==(35,83,65,18)
assert sum(c['exhaustiveTheorems'] for c in certs)==270
assert sum(c['requiredProofValueEdges'] for c in certs)==145
assert len(json.loads((r/'Tools/scaffold.json').read_text(encoding='utf-8'))['productionModules'])==9149
assert not (p/'source-gamma-one-diamond-quotient-production-build-9161.log').exists()
assert not (p/'gamma-one-diamond-quotient-preflight-9161.json').exists()
digests={n:sha(p/n) for n in names}
for c in certs:
 assert c['exit']==c['diagnostics']==0
 for row in c['files']:assert sha(Path(row['path']))==row['sha256']
dependency='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> automorphy -> original all-weight characteristic-zero association -> actual homogeneous Gamma1 Tate quotient, original finite Hecke character and the required degree/genus comparison.'
discharged='The actual diamond-one homogeneous Tate quotient has a finite continuous Galois action, derived original Hecke stability and a Frobenius polynomial from separate original degree/genus equalities. The native Tate/H1 transfer descends to this quotient; the original integral parabolic-transfer input and primitive form character imply its nonvanishing away from the stated fixed exception. Original full-word compatibility constructs a unital character on the literal quotient operator algebra, with the original adic eigenvalues, and its Galois/Hecke commutation and chosen local Frobenius polynomial. No operator descent, character or nonzero vector is assumed. Independently, actual residue integral modular-form ratios embed in the native residue field, the literal reduced j belongs to that ratio field, and their coordinate degrees satisfy the necessary upper bounds. A native consumer derives degree equality and equality of the actual residue fields from the exact signed-index lower bound. Actual weight-four Gamma1 Eisenstein forms now have integral Fourier expansions and the exact Gamma0 slash action. Their ratios with the original E4 distinguish the identity signed diamond class at every coefficient characteristic for levels greater than two.'
boundary='Original degree and genus preservation remain unproved and explicit in the quotient Frobenius/Hecke/character construction. The integral parabolic-preimage theorem remains open; full-H1 surjectivity does not replace it. The transfer retains 3<p and the fixed exceptional-prime exclusion. Integral Eisenstein separation does not yet supply the action on every reduced rational relation: level-power slash integrality or a rigorous replacement, the signed-index lower bound and the genus argument remain. The required two-dimensional characteristic-zero realization, exceptional coefficient primes, original all-weight association, remaining local/image/regularity inputs, automorphy and literal higher continuation remain required. Acceptance stays 16/20; DUB-17--20 OPEN; every original acceptance test is unchanged.'
route='Native Picard/Tate, coefficient, cyclotomic, continuous finite Galois, quotient, original cohomology transfer and parabolic congruence proofs are reused. The quotient polynomial derives Hecke stability; native free-algebra word intertwining yields the character. The new residue comparison reuses the original Gauss map, j and scalar-extension identities. For Eisenstein separation, summing the second residue classes first reuses Mathlib Lipschitz and divisor-product identities and avoids general additive-character Fourier calculations; Gamma1 specialization avoids general GammaH coset averaging. The targeted source review is refined by the exact Fricke/peaked-auxiliary integrality chain. Five independently audited scratch scopes are promoted together, preserving all focused checks and a single sequential foundation/paper verification. The unused 9,161-module plan is superseded before any production mutation. All proof bodies and comments remain identical after import qualification; frozen source, root pins and owner-only BAT are unchanged.'
status='The thirty-five-module scope passes 83 public axiom queries, 270 exhaustive scratch theorem checks, sixteen linters per module and five declaration-value audits with 145 required dependency checks, with zero diagnostics. Production aggregate, focused audits and sequential foundation/paper verification of the 9,184-module scope are pending.'
report='Dubon Original Gamma One Hecke and Separation Assessment 2026-10-28.md'
routefile='gamma-one-hecke-separation-promotion-route-1505.json'
def output(n,t):
 f=p/n;assert not f.exists(),f;f.write_text(t,encoding='utf-8')
output(report,'# Original Gamma1 Hecke characters and integral separation — 28 October 2026\n\n'+discharged+'\n\n'+status+'\n\nThe source dependency is '+dependency+'.\n\n'+boundary+'\n\n'+route+'\n\nIndividual scratch receipts retain the exact statements, assumptions, public/private/generated audits, linter scopes and proof-value closures. The residue comparison and integral Eisenstein results impose no degree/genus hypothesis. They are prerequisites for proving those geometric equalities, not substitutes for them.\n')
output(routefile,json.dumps(dict(recordedUTC=datetime.now(timezone.utc).isoformat(),dependency=dependency,discharged=discharged,remaining=boundary,route=route,receipts=digests,modules=35,queries=83,exhaustiveScratchChecks=270,proofValueChecks=145,scopes=5,productionMutation=False,supersededUnusedPlan=9161),indent=2)+'\n')
subs={'GammaOneDiamondQuotient':'GammaOneHeckeSeparation','gamma_one_diamond_quotient':'gamma_one_hecke_separation','gamma-one-diamond-quotient':'gamma-one-hecke-separation','9161':'9184','9,161':'9,184','20261028-1453':'20261028-1505'}
pat=re.compile('|'.join(re.escape(x) for x in sorted(subs,key=len,reverse=True)))
tr=lambda t:pat.sub(lambda m:subs[m[0]],t)
t=tr((p/'integrate_source_gamma_one_diamond_quotient_9161.py').read_text(encoding='utf-8'))
t=re.sub(r'^digests = .+$',lambda _:'digests = '+repr(digests),t,flags=re.M)
t=t.replace('(12, 12, 27, 22, 5)','(35, 35, 83, 65, 18)').replace('assert count == 100','assert count == 270')
t=t.replace('"increment": 12, "queries": 27','"increment": 35, "queries": 83')
for key,val in [('dependency',dependency),('discharged',discharged),('boundary',boundary),('route',route),('status',status)]:
 t=re.sub(r'^'+key+r' = .+$',lambda _,key=key,val=val:key+' = '+repr(val),t,flags=re.M)
t=t.replace('Original Gamma One diamond quotient and transfer','Original Gamma One Hecke characters and integral separation')
evidence=names+[s+'-audit-config.json' for s in stems]+[routefile]
owners=[Path(c['ownershipLog']).stem for c in certs]
for c in certs:
 for key in ['log','dependencyAuditLog','ownershipLog']:
  f=Path(c[key]);evidence += [f.with_suffix(e).name for e in ['.lean','.log','.exit']]
 for row in c['files']:evidence += [Path(row['path']).name,Path(row['compileLog']).name,Path(row['compileExit']).name]
 rv=Path(c['reuseReview']);evidence.append(rv.name)
 evidence.append(Path(json.loads(rv.read_text(encoding='utf-8'))['routeAssessment']['path']).name)
versionfiles=['gamma-one-diamond-versions-1441.json','gamma-one-transfer-versions-1446.json',
'gamma-one-quotient-character-versions-1460.json','gamma-one-integral-ratio-versions-1480.json',
'gamma-one-integral-eisenstein-versions-1500.json']
for vf in versionfiles:
 evidence.append(vf)
 for m,v in json.loads((p/vf).read_text(encoding='utf-8')).items():
  # One version-map alias intentionally preserves an older arithmetic field module.
  if m=='SourceGammaOneArithmeticDiamondPolynomial':m='SourceGammaOneArithmeticDiamond'
  pattern=re.compile(re.escape(m)+r'\d+[a-z]?(?:\.lean(?:\.txt)?|\.log|\.exit)$')
  evidence += [f.name for f in p.iterdir() if f.is_file() and pattern.fullmatch(f.name)]
evidence += ['gamma-one-diamond-version-aliases-1441.json','gamma-one-diamond-quotient-preexecution-correction-1453b.json','gamma-one-diamond-scope-preexecution-correction-1475.json','integral-slash-dependency-review-1501.json']
individualReports=['Dubon Original Gamma One Diamond Quotient Assessment 2026-10-28.md',
'Dubon Original Gamma One Quotient Character Assessment 2026-10-28.md','Dubon Integral Eisenstein Reuse Assessment 2026-10-28.md']
evidence += individualReports
for n in ['anthropic-integral-slash-depth-1495','anthropic-fricke-integrality-depth-1496','anthropic-peaked-integrality-depth-1498']:
 evidence += [f.relative_to(p).as_posix() for f in (p/n).rglob('*') if f.is_file()]
for f in p.iterdir():
 if f.is_file() and f.suffix in ['.py','.ps1','.json'] and (re.search(r'(?:14[3-9]\d|150[01])[a-z]?\.',f.name)) and f.name.startswith(('prepare_gamma_one_','prepare_integral_','prepare_quotient_','build_gamma_one_','audit_gamma_one_','record_gamma_one_','revise_gamma_one_','revise_eisenstein_','revise_integral_eisenstein_','correct_diamond_','correct_gamma_one_','fetch_eisenstein_','fetch_fricke_integrality_','fetch_peaked_','prepare_fricke_integrality_','prepare_peaked_')):evidence.append(f.name)
for n in evidence:assert (p/n).exists(),n
a=t.index('evidence=[p/');b=t.index('for cert in certs:\n    evidence.append',a)
t=t[:a]+'evidence=[p/n for n in '+repr(sorted(set(evidence)))+']\n'+t[b:]
t=t.replace('gamma-one-hecke-separation-promotion-route-1453.json',routefile)
t=t.replace("p / 'Dubon Original Gamma One Diamond Quotient Assessment 2026-10-28.md'",'p / '+repr(report))
t=re.sub(r"assert sha\(reportSource\) == '[A-F0-9]+'",lambda _:'assert sha(reportSource) == '+repr(sha(p/report)),t)
# Preserve individual reports as dated research evidence; the combined report tracks assembled status.
point=t.index('audit = r / "Extension/Dubon2026/Audit.lean"')
extra="for name in "+repr(individualReports)+":\n    target=r/name\n    assert not target.exists(),target\n    refresh_pending.append((target,(p/name).read_bytes(),'root'))\n\n"
t=t[:point]+extra+t[point:]
oldedge=next(x for x in (r/'Dubon Architecture.md').read_text(encoding='utf-8').splitlines() if x.startswith('  GAMMAGALOIS9149['))
newedge='  GAMMAGALOIS9149["Actual continuous finite homogeneous Tate Galois action and faithful finite factor; conditional arithmetic descent (DUB-17/18)"] --> GAMMAHECKE9184\n  GAMMAHECKE9184["Actual diamond quotient and original adic operator character from degree/genus/parabolic inputs; integral residue comparison and all-characteristic Eisenstein separators proved. Field action, degree/genus, parabolic transfer, two-dimensional realization and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
t=re.sub(r'^edge = .+$',lambda _:'edge = '+repr(oldedge),t,flags=re.M)
t=re.sub(r'^arch.write_text\(.*$',lambda _:"arch.write_text(arch.read_text(encoding='utf-8').replace(edge,"+repr(newedge)+"),encoding='utf-8')",t,flags=re.M)
a=t.index("b = re.sub('  logInfo");b=t.index(', b)',a)+len(', b)')
line='  logInfo m!"SOURCE GAMMA ONE HECKE SEPARATION AUDIT PASS: {count} theorems including private/generated declarations. Actual quotient and original adic operator character from separate geometric/parabolic inputs; original residue comparison and integral Eisenstein separation proved. Remaining source gates OPEN;16/20 gates."\n'
t=t[:a]+'b = re.sub('+repr('  logInfo m!".*"\n')+', '+repr(line)+', b)'+t[b:]
scripts=[]
def script(n,t):
 if n.endswith('.py'):ast.parse(t)
 output(n,t);scripts.append(n)
script('integrate_source_gamma_one_hecke_separation_9184.py',t)
for n in ['prepare_gamma_one_diamond_quotient_production_ownership_9161.py','prepare_gamma_one_diamond_quotient_global_ownership_9161.py']:
 script(tr(n),tr((p/n).read_text(encoding='utf-8')))
t=tr((p/'compare_gamma_one_diamond_quotient_ownership_9161.py').read_text(encoding='utf-8'))
t=t.replace('len(names)==len(certs)==2','len(names)==len(certs)==5').replace('len(set(allmods))==12','len(set(allmods))==35').replace("result['scratchSum']==100","result['scratchSum']==270").replace('All 12 mathematical','All 35 mathematical')
script('compare_gamma_one_hecke_separation_ownership_9184.py',t)
t=tr((p/'record_source_gamma_one_diamond_quotient_9161.py').read_text(encoding='utf-8'))
t=re.sub(r'\b100\b','270',t);t=re.sub(r'\b12\b','35',t)
t=t.replace('len(ownershipComparison["scopes"]) == 2','len(ownershipComparison["scopes"]) == 5')
t=t.replace('Two declaration-value audits verify 51','Five declaration-value audits verify 145').replace('int(a[2]) == 26717','int(a[2]) == 26760')
t=t.replace('Dubon Original Gamma One Diamond Quotient Assessment 2026-10-28.md',report).replace('GAMMA ONE DIAMOND QUOTIENT','GAMMA ONE HECKE SEPARATION').replace('original Gamma One diamond quotient and transfer','original Gamma One Hecke characters and integral separation')
script('record_source_gamma_one_hecke_separation_9184.py',t)
for prefix in ['build','verify']:
 script(prefix+'_gamma_one_hecke_separation_9184.ps1',tr((p/(prefix+'_gamma_one_diamond_quotient_9161.ps1')).read_text(encoding='utf-8')))
t=tr((p/'archive_gamma_one_diamond_quotient_canonical_9161.py').read_text(encoding='utf-8'))
t=t.replace('original Gamma One actual diamond-one quotient, derived original Hecke stability and Frobenius, original transfer and conditional nonvanishing','original Gamma One diamond quotient and operator character, actual residue comparison and integral Eisenstein separation')
script('archive_gamma_one_hecke_separation_canonical_9184.py',t)
t=tr((p/'preflight_gamma_one_diamond_quotient_9161.py').read_text(encoding='utf-8'))
t=t.replace("==12 and len(ns['queries'])==27 and ns['count']==100","==35 and len(ns['queries'])==83 and ns['count']==270").replace('modules=12,queries=27,exhaustiveScratchChecks=100,proofValueChecks=51','modules=35,queries=83,exhaustiveScratchChecks=270,proofValueChecks=145')
script('preflight_gamma_one_hecke_separation_9184.py',t)
output('source-gamma-one-hecke-separation-scratch-ownership-9184.json',json.dumps(owners,indent=2)+'\n')
output('gamma-one-hecke-separation-preexecution-review-9184.json',json.dumps(dict(status='Prepared only. Predecessor 9149 canonical PASS and archive required. Unused 9161 plan superseded before production mutation.',modules=35,queries=83,theorems=65,constructions=18,exhaustiveScratchChecks=270,proofValueChecks=145,scopes=5,receipts=digests,expectedConsumers=26760,expectedConstructions=2881,fullGoal=boundary,scripts=[dict(path=str(p/n),sha256=sha(p/n)) for n in scripts],productionMutation=False),indent=2)+'\n')
print(json.dumps(dict(scripts=len(scripts),modules=35,checks=270,proofEdges=145,productionMutation=False)))
