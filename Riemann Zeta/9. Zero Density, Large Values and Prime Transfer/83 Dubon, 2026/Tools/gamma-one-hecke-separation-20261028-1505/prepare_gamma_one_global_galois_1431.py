from pathlib import Path
from datetime import datetime, timezone
import ast,hashlib,json,re
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
stems=['source-gamma-one-twisted-1','source-gamma-one-continuity-1','source-gamma-one-arithmetic-orbit-2']
names=[s+'-scratch-receipt.json' for s in stems]
certs=[json.loads((p/n).read_text(encoding='utf-8')) for n in names]
assert tuple(sum(len(c[k]) for c in certs) for k in ['modules','queries','theoremRegistrations','constructionRegistrations'])==(26,39,33,6)
total=sum(c['exhaustiveTheorems'] for c in certs)
edges=sum(c['requiredProofValueEdges'] for c in certs);assert edges==80
digests={n:sha(p/n) for n in names}
dependency='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> finite Gamma1 Hecke-character realization -> the actual continuous homogeneous-valued Tate Galois action, prescribed-support descent and original parabolic Frobenius polynomial.'
discharged='The actual cyclotomic character and original Picard Tate action now construct a genuine Galois representation on the finite homogeneous-valued Tate dual in every weight. Original finite fields of definition, open Picard stabilizers, uniform Tate congruences and the existing primitive-root continuity theorem prove continuity and a faithful finite Galois factor, without geometric degree/genus assumptions. Exact local cyclotomic values and the original norm-derived Tate relation give its Frobenius polynomial; the actual local inertia acts trivially when the original coordinate degree and genus are preserved. The existing continuous unit lift and prescribed-support quotient theorem then derive arithmetic descent from those two separate geometric families. The representation commutes with the actual good-prime Hecke and combined-diamond operators. The literal restriction of every original parabolic class has a Tate lift with derived combined-diamond fixedness, and the Frobenius polynomial holds throughout its Galois orbit in the existing comparison range 3<p. No continuity, finite Galois factor, unit lift, inertia identity, arithmetic descent, cyclotomic value, diamond fixedness or Frobenius relation is assumed in these consumers.'
boundary='Actual Gamma1 j-coordinate degree equality and genus preservation remain open and explicit in the local and arithmetic-descent consumers. The finite Tate-dual action and its faithful finite Galois factor do not yet give the required two-dimensional Hecke-character realization. Nonzero original parabolic character realization/transfer or a faithful alternative, exceptional coefficient primes, coefficient-field realization, original all-weight characteristic-zero association, local/image/regularity, automorphy and literal higher symmetric-power continuation remain. The parabolic Tate comparison retains 3<p; the continuity/finite-factor proof does not impose that restriction. The earlier differently normalized untwisted conditional relation is not claimed discharged. Acceptance stays 16/20; DUB-17--20 OPEN; all twenty acceptance tests are unchanged.'
route='The October 28 upstream refresh and native proof search were checked before each dependency expansion. The actual homogeneous matrix representation, primitive-root cyclotomic character, original finite function/place/Picard fields, exact Tate projection kernel and period basis, native finite fixed-field theorem, adopted Imperial continuous unit lift, actual local valuation transport and original arithmetic quotient descent are reused. Original parabolic restriction and the proved Tate/H1 equivalence derive diamond fixedness; a minimal diagonal commutation gives its Galois stability. Generic narrow consumers resolve concrete elaboration costs without increasing proof limits. The full-H1 transfer surjectivity is not treated as parabolic transfer surjectivity. All promoted mathematical bodies and comments remain identical to their audited forms after import qualification; frozen sources, root pins and the owner-only BAT are unchanged.'
status=f'The twenty-six-module scope passes 39 public axiom queries, {total} exhaustive scratch theorem checks, sixteen linters per module and three declaration-value audits with 80 required dependency checks, with zero diagnostics. Production aggregate, focused audits and sequential foundation/paper verification of the 9,149-module scope are pending.'
report='Dubon Original Gamma One Global Galois Assessment 2026-10-28.md'
routefile='gamma-one-global-galois-promotion-route-1431.json'
def output(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output(report,'# Original Gamma One global Galois realization — 28 October 2026\n\n'+discharged+'\n\n'+dependency+'\n\n'+route+'\n\n'+status+'\n\n'+boundary+'\n\nThe [fresh reuse refresh](Dubon%20Reuse%20Refresh%202026-10-28.md) and [curve supplement](Dubon%20Curve%20Reuse%20Supplement%202026-10-28.md) distinguish inspected upstream sources from adopted proofs. Exact source snapshots, unsuccessful elaboration attempts, successful successors and all checks are preserved in `Tools/gamma-one-global-galois-20261028-1431/`.\n')
output(routefile,json.dumps(dict(recordedUTC=datetime.now(timezone.utc).isoformat(),dependency=dependency,discharged=discharged,remaining=boundary,route=route,receipts=digests,modules=26,queries=39,exhaustiveScratchChecks=total,proofValueChecks=80,productionMutation=False),indent=2)+'\n')
subs={'GammaOneTateFrobenius':'GammaOneGlobalGalois','gamma_one_tate_frobenius':'gamma_one_global_galois','gamma-one-tate-frobenius':'gamma-one-global-galois','GammaOnePicardReduction':'GammaOneTateFrobenius','gamma_one_picard_reduction':'gamma_one_tate_frobenius','gamma-one-picard-reduction':'gamma-one-tate-frobenius','9123':'9149','9097':'9123','9,123':'9,149','9,097':'9,123','20261028-1402':'20261028-1431','20261028-1358':'20261028-1402'}
pat=re.compile('|'.join(re.escape(x) for x in sorted(subs,key=len,reverse=True)))
tr=lambda s:pat.sub(lambda m:subs[m[0]],s)
s=tr((p/'integrate_source_gamma_one_tate_frobenius_9123.py').read_text(encoding='utf-8'))
s=re.sub(r'^digests = .+$',lambda _:'digests = '+repr(digests),s,flags=re.M)
s=s.replace('(26, 26, 49, 45, 4)','(26, 26, 39, 33, 6)').replace('assert count == 81',f'assert count == {total}')
s=s.replace('"increment": 26, "queries": 49','"increment": 26, "queries": 39')
for key,val in [('dependency',dependency),('discharged',discharged),('boundary',boundary),('route',route),('status',status)]:s=re.sub(r'^'+key+r' = .+$',lambda _,key=key,val=val:key+' = '+repr(val),s,flags=re.M)
s=s.replace('Original Gamma One inertia and Tate Frobenius','Original Gamma One global Galois realization')
s=s.replace('The original Gamma1 fields, literal norm and diamond conventions, every residue-invertible Tate prime, every homogeneous weight, and the explicit coordinate-degree and genus hypotheses are retained.','The original Gamma1 fields, actual homogeneous coefficients, cyclotomic character and Picard Tate action are retained. The local coordinate-degree/genus hypotheses and the parabolic comparison range are explicit; continuity and finite factorization impose no additional geometric hypothesis.')
evidence=names+[n+'-audit-config.json' for n in stems]
owners=[Path(c['ownershipLog']).stem for c in certs]
for c in certs:
 for key in ['log','dependencyAuditLog']:
  f=Path(c[key]);evidence += [f.with_suffix(e).name for e in ['.lean','.log','.exit']]
 for row in c['files']:evidence += [Path(row['path']).name,Path(row['compileLog']).name,Path(row['compileExit']).name]
 evidence.append(Path(c['reuseReview']).name)
 rv=json.loads(Path(c['reuseReview']).read_text(encoding='utf-8'));evidence.append(Path(rv['routeAssessment']['path']).name)
pattern=r'(?<!\d)(?:'+'|'.join(str(i) for i in range(1398,1431))+r')[a-z]?(?!\d)'
for f in p.iterdir():
 if f.is_file() and f.suffix in ['.json','.py','.ps1','.txt','.log','.exit','.lean','.md'] and re.search(pattern,f.name):evidence.append(f.name)
for n in owners:evidence += [n+e for e in ['.lean','.log','.exit']]
evidence += ['source-gamma-one-arithmetic-orbit-1-audit-config.json','SourceGammaOneArithmeticOrbitDependencyAudit1.lean','SourceGammaOneArithmeticOrbitDependencyAudit1.log','SourceGammaOneArithmeticOrbitDependencyAudit1.exit']
folders=[f.name for f in p.iterdir() if f.is_dir() and re.search(pattern+r'$',f.name) and f.name.startswith('gamma-one-')]
for n in evidence+folders:assert (p/n).exists(),n
a=s.index('evidence=[p/');b=s.index('for cert in certs:\n    evidence.append',a)
s=s[:a]+'evidence=[p/'+repr(routefile)+']\nevidence += [p/n for n in '+repr(sorted(set(evidence)))+']\nfor folder in '+repr(folders)+':\n    evidence += sorted(f for f in (p/folder).rglob("*") if f.is_file())\n'+s[b:]
s=s.replace('gamma-one-global-galois-promotion-route-1402.json',routefile)
s=s.replace("p / 'Dubon Original Gamma One Tate Frobenius Assessment 2026-10-28.md'",'p / '+repr(report))
s=re.sub(r"assert sha\(reportSource\) == '[A-F0-9]+'",lambda _:'assert sha(reportSource) == '+repr(sha(p/report)),s)
oldedge=next(x for x in (r/'Dubon Architecture.md').read_text(encoding='utf-8').splitlines() if x.startswith('  GAMMATATE9123['))
newedge='  GAMMATATE9123["Original norm-derived Tate Frobenius and inertia from degree/genus equality (DUB-17/18)"] --> GAMMAGALOIS9149\n  GAMMAGALOIS9149["Actual finite homogeneous Tate Galois action: continuity and faithful finite factor proved; arithmetic descent and parabolic Galois-orbit Frobenius from degree/genus equality. Geometric equalities, nonzero character/two-dimensional realization and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
s=re.sub(r'^edge = .+$',lambda _:'edge = '+repr(oldedge),s,flags=re.M)
s=re.sub(r'^arch.write_text\(.*$',lambda _:"arch.write_text(arch.read_text(encoding='utf-8').replace(edge,"+repr(newedge)+"),encoding='utf-8')",s,flags=re.M)
a=s.index("b = re.sub('  logInfo");b=s.index(', b)',a)+len(', b)')
line='  logInfo m!"SOURCE GAMMA ONE GLOBAL GALOIS AUDIT PASS: {count} theorems including private/generated declarations. Actual continuous finite homogeneous Tate Galois action and faithful finite factor; original arithmetic descent and parabolic Galois-orbit Frobenius from coordinate-degree/genus equality. Actual geometric equalities and nonzero two-dimensional Hecke-character realization remain;16/20 gates."\n'
s=s[:a]+'b = re.sub('+repr('  logInfo m!".*"\n')+', '+repr(line)+', b)'+s[b:]
scripts=[]
def script(n,s):
 if n.endswith('.py'):ast.parse(s)
 output(n,s);scripts.append(n)
script('integrate_source_gamma_one_global_galois_9149.py',s)
for n in ['prepare_gamma_one_tate_frobenius_production_ownership_9123.py','prepare_gamma_one_tate_frobenius_global_ownership_9123.py']:script(tr(n),tr((p/n).read_text(encoding='utf-8')))
s=tr((p/'compare_gamma_one_tate_frobenius_ownership_9123.py').read_text(encoding='utf-8'))
s=s.replace("result['scratchSum']==81",f"result['scratchSum']=={total}")
script('compare_gamma_one_global_galois_ownership_9149.py',s)
s=tr((p/'record_source_gamma_one_tate_frobenius_9123.py').read_text(encoding='utf-8'))
s=re.sub(r'\b81\b',str(total),s)
s=s.replace('Three declaration-value audits verify 99','Three declaration-value audits verify 80').replace('int(a[2]) == 26662','int(a[2]) == 26695')
s=s.replace('Dubon Original Gamma One Tate Frobenius Assessment 2026-10-28.md',report)
s=s.replace('GAMMA ONE TATE FROBENIUS','GAMMA ONE GLOBAL GALOIS').replace('original Gamma One inertia and Tate Frobenius','original Gamma One global Galois realization')
script('record_source_gamma_one_global_galois_9149.py',s)
for prefix in ['build','verify']:script(prefix+'_gamma_one_global_galois_9149.ps1',tr((p/(prefix+'_gamma_one_tate_frobenius_9123.ps1')).read_text(encoding='utf-8')))
s=tr((p/'archive_gamma_one_tate_frobenius_canonical_9123.py').read_text(encoding='utf-8'))
s=s.replace('original Gamma One conditional inertia, norm-derived Tate Frobenius and inverse-action all-weight polynomial','original Gamma One continuous finite homogeneous Tate Galois action, faithful finite factor, conditional prescribed arithmetic descent and parabolic Galois-orbit Frobenius')
script('archive_gamma_one_global_galois_canonical_9149.py',s)
s=tr((p/'preflight_gamma_one_tate_frobenius_9123.py').read_text(encoding='utf-8'))
s=s.replace("==26 and len(ns['queries'])==49 and ns['count']==81",f"==26 and len(ns['queries'])==39 and ns['count']=={total}")
s=s.replace('modules=26,queries=49,exhaustiveScratchChecks=81,proofValueChecks=99',f'modules=26,queries=39,exhaustiveScratchChecks={total},proofValueChecks=80')
script('preflight_gamma_one_global_galois_9149.py',s)
output('source-gamma-one-global-galois-scratch-ownership-9149.json',json.dumps(owners,indent=2)+'\n')
output('gamma-one-global-galois-preexecution-review-9149.json',json.dumps(dict(status='Prepared only. Integration requires predecessor canonical PASS and archive.',modules=26,queries=39,theorems=33,constructions=6,exhaustiveScratchChecks=total,proofValueChecks=80,scopes=3,receipts=digests,expectedConsumers=26695,expectedConstructions=2863,fullGoal=boundary,scripts=[dict(path=str(p/n),sha256=sha(p/n)) for n in scripts],productionMutation=False),indent=2)+'\n')
print(json.dumps(dict(scripts=len(scripts),modules=26,checks=total,proofEdges=80,productionMutation=False)))
