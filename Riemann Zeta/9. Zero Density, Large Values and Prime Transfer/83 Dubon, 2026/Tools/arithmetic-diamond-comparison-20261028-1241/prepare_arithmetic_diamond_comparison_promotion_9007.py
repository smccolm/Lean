from pathlib import Path
from datetime import datetime,timezone
import json,re,hashlib,ast
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
stems=['source-gamma-one-diamond-field-1','source-gamma-one-arithmetic-diamond-1',
 'source-diamond-picard-periods-1','source-diamond-galois-1','source-diamond-normalizer-1']
names=[s+'-scratch-receipt.json' for s in stems]
certs=[json.loads((p/n).read_text(encoding='utf-8')) for n in names]
assert tuple(sum(len(c[k]) for c in certs) for k in ['modules','queries','theoremRegistrations','constructionRegistrations'])==(39,111,92,19)
total=sum(c['exhaustiveTheorems'] for c in certs);edges=sum(c['requiredProofValueEdges'] for c in certs)
assert edges==172
digests={n:sha(p/n) for n in names}
dependency='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> arithmetic realization of original finite Gamma1 homogeneous-coefficient Hecke characters -> original arithmetic diamond, Picard/period/Tate comparison, Galois commutation and exact homogeneous normalizer coefficient convention.'
discharged='The literal Gamma0 diamond is constructed on the original complex modular-ratio field and descended to the original algebraic-closure field. Its original j-coordinate, constants, quotient and cusp-germ identities are proved. The actual field action induces the original place, divisor and Picard action. Existing analytic representatives and the moving lemma prove the complete complex Picard-period square, including the degree-zero cancellation of the basepoint term; unique constant-field place extension proves the arithmetic conorm square. The same arithmetic diamond therefore acts on the original Picard Tate module and integral period tensor as the actual dual slash diamond. Cyclotomic Fricke covariance, rational fixed-field descent and genuine rational cusp quotients prove rationality of diamond images of the original integral modular-ratio generators, discharging all auxiliary fraction and germ inputs. Original field generation then proves Galois commutation on both fields and on the original arithmetic places, divisors, Picard group and Tate module. The actual diagonal-cover normalizer determines the inverse original binary coefficient action; it fixes literal restrictions of original cocycles and H1 classes, equals homogeneous substitution by the reversed diagonal entries modulo the coefficient modulus, and depends only on the lower-right unit label. The original arithmetic Tate dual/H1 diamond comparison consumes precisely that coefficient formula and commutes with Galois. No replacement modular-curve or coefficient model is introduced.'
boundary='The original arithmetic diamond, full Picard/period/Tate compatibility, Galois commutation and homogeneous normalizer coefficient convention are now proved. The exact geometric lifting condition sourceGammaOneIntegralParabolicTransfer remains unproved, so the existing finite parabolic character descent remains conditional and excludes primes dividing its fixed nonzero integer. Exceptional primes, coefficient-field/Frobenius/inertia realization, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain. Finite characters do not supply a characteristic-zero lift. 16/20; DUB-17--20 OPEN; all twenty acceptance gates unchanged.'
route='The October 28 upstream refresh supplied the single-coset diamond route, adapted to the existing native objects. Before extending dependencies, reuse checks selected original modular quotients and injective cusp germs for the complex field, a native linear coefficient projection and finite-span quotient argument for scalar intersection, and the original finite j-relation for arithmetic descent. Existing analytic Picard surjectivity avoids a new cusp-by-cusp presentation. Existing cyclotomic Fricke covariance and rational cusp normalization avoid a new rational modular-curve model or automorphism extension to C. Native cocycle identities and the already proved diagonal-cover triviality identify the actual coefficient convention. The exact original arithmetic Tate/H1 consumer then composes those results. Historical scratch receipts retain their then-open obligations; the current assembled assessment supersedes those boundaries. Frozen mathematical bodies are promoted by import qualification only.'
status=f'The thirty-nine-module original arithmetic diamond and homogeneous comparison scope passes 111 public axiom queries, {total} exhaustive scratch theorem checks, sixteen linters per module and five declaration-value audits with 172 required dependency checks, with zero diagnostics. Production aggregate, focused audits and sequential foundation/paper verification of the 9,007-module scope are pending.'
report='Dubon Arithmetic Diamond Reuse Assessment 2026-10-28.md'
routefile='arithmetic-diamond-comparison-promotion-route-1241.json'
def output(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output(report,'# Dubon original arithmetic diamond comparison assessment — 28 October 2026\n\n'+discharged+'\n\n'+dependency+'\n\n'+route+'\n\n'+status+'\n\n'+boundary+'\n\nThe [nine-repository refresh](Dubon%20Reuse%20Refresh%202026-10-28.md) records the inspected fixed revisions and their limitations. The five exact dependency assessments and scratch evidence are preserved in `Tools/arithmetic-diamond-comparison-20261028-1241/`. Root pins, the frozen paper and the owner-only synchronization BAT are unchanged.\n')
output(routefile,json.dumps(dict(recordedUTC=datetime.now(timezone.utc).isoformat(),dependency=dependency,discharged=discharged,remaining=boundary,route=route,receipts=digests,modules=39,queries=111,exhaustiveScratchChecks=total,proofValueChecks=172,productionMutation=False),indent=2)+'\n')
def tr(s):
 for a,b in [('ParabolicDiamondComparison','ArithmeticDiamondComparison'),('parabolic_diamond_comparison','arithmetic_diamond_comparison'),('parabolic-diamond-comparison','arithmetic-diamond-comparison'),('GammaOneHomogeneousParabolic','ParabolicDiamondComparison'),('gamma_one_homogeneous_parabolic','parabolic_diamond_comparison'),('gamma-one-homogeneous-parabolic','parabolic-diamond-comparison'),('8968','9007'),('8947','8968'),('8,968','9,007'),('8,947','8,968'),('20261028-1196','20261028-1241'),('20261028-1163','20261028-1196')]:s=s.replace(a,b)
 return s
s=tr((p/'integrate_source_parabolic_diamond_comparison_8968.py').read_text(encoding='utf-8'))
s=re.sub(r'^digests = .+$',lambda _:'digests = '+repr(digests),s,flags=re.M)
s=s.replace('(21, 21, 61, 46, 15)','(39, 39, 111, 92, 19)').replace('assert count == 108',f'assert count == {total}').replace('"increment": 21, "queries": 61','"increment": 39, "queries": 111')
for key,val in [('dependency',dependency),('discharged',discharged),('boundary',boundary),('route',route),('status',status)]:s=re.sub(r'^'+key+r' = .+$',lambda _,key=key,val=val:key+' = '+repr(val),s,flags=re.M)
s=s.replace('Original parabolic operator congruence, conditional finite character descent and native/period diamond comparison','Original arithmetic diamond, Galois and homogeneous coefficient comparison')
evidence=names+[n+'-audit-config.json' for n in stems]
owners=[Path(c['ownershipLog']).stem for c in certs]
for c in certs:
 for key in ['log','dependencyAuditLog']:
  f=Path(c[key]);evidence += [f.with_suffix(e).name for e in ['.lean','.log','.exit']]
 for row in c['files']:evidence += [Path(row['path']).name,Path(row['compileLog']).name,Path(row['compileExit']).name]
 evidence.append(Path(c['reuseReview']).name)
 rv=json.loads(Path(c['reuseReview']).read_text(encoding='utf-8'));rf=Path(rv['routeAssessment']['path']);evidence.append(rf.name)
 for row in json.loads(rf.read_text(encoding='utf-8')).get('reuseChecked',[]):
  f=Path(row['path'])
  if f.is_relative_to(p):evidence.append(str(f.relative_to(p)))
pattern=r'(?<!\d)(?:'+'|'.join(str(i) for i in range(1197,1242))+r')[a-z]?(?!\d)'
for f in p.iterdir():
 if f.is_file() and f.suffix in ['.json','.py','.ps1','.txt','.log','.exit','.lean','.md'] and re.search(pattern,f.name):evidence.append(f.name)
for n in owners:evidence += [n+e for e in ['.lean','.log','.exit']]
folders=[f.name for f in p.iterdir() if f.is_dir() and re.search(pattern+r'$',f.name)]
for n in evidence+folders:assert(p/n).exists(),n
a=s.index('evidence=[p/');b=s.index("for cert in certs:\n    evidence.append",a)
s=s[:a]+'evidence=[p/'+repr(routefile)+']\nevidence += [p/n for n in '+repr(sorted(set(evidence)))+']\nfor folder in '+repr(folders)+':\n    evidence += sorted(f for f in (p/folder).rglob("*") if f.is_file())\n'+s[b:]
s=s.replace('arithmetic-diamond-comparison-promotion-route-1196.json',routefile)
s=s.replace("p / 'Dubon Parabolic Character and Diamond Reuse Assessment 2026-10-28.md'","p / "+repr(report))
s=re.sub(r"assert sha\(reportSource\) == '[A-F0-9]+'",lambda _:"assert sha(reportSource) == "+repr(sha(p/report)),s)
oldedge=next(x for x in (r/'Dubon Architecture.md').read_text(encoding='utf-8').splitlines() if x.startswith('  PARABDIAM8968['))
newedge='  PARABDIAM8968["Original parabolic congruences away from a fixed integer, finite parabolic/Tate word kernel, conditional transfer descent and native/period diamonds proved (DUB-17/18)"] --> ARITHDIAM9007\n  ARITHDIAM9007["Original arithmetic field/Picard/period/Tate diamonds, Galois commutation, exact homogeneous normalizer coefficient action and native finite H1 comparison proved. Parabolic transfer preimages, exceptional primes, Frobenius/inertia, characteristic-zero association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
s=re.sub(r'^edge = .+$',lambda _:'edge = '+repr(oldedge),s,flags=re.M)
s=re.sub(r'^arch.write_text\(.*$',lambda _:"arch.write_text(arch.read_text(encoding='utf-8').replace(edge,"+repr(newedge)+"),encoding='utf-8')",s,flags=re.M)
a=s.index("b = re.sub('  logInfo");b=s.index(', b)',a)+len(', b)')
line='  logInfo m!"SOURCE ARITHMETIC DIAMOND COMPARISON AUDIT PASS: {count} theorems including private/generated declarations. Original arithmetic field/Picard/period/Tate diamonds, actual Galois commutation, exact homogeneous normalizer coefficients and native finite H1 comparison. Parabolic transfer preimages, exceptional primes, Frobenius/inertia and characteristic-zero association remain;16/20 gates."\n'
s=s[:a]+'b = re.sub('+repr('  logInfo m!".*"\\n')+', '+repr(line)+', b)'+s[b:]
scripts=[]
def script(n,s):
 if n.endswith('.py'):ast.parse(s)
 output(n,s);scripts.append(n)
script('integrate_source_arithmetic_diamond_comparison_9007.py',s)
for n in ['prepare_parabolic_diamond_comparison_production_ownership_8968.py','prepare_parabolic_diamond_comparison_global_ownership_8968.py']:script(tr(n),tr((p/n).read_text(encoding='utf-8')))
s=tr((p/'compare_parabolic_diamond_comparison_ownership_8968.py').read_text(encoding='utf-8'))
s=s.replace('==21','==39').replace('==7','==5').replace("result['scratchSum']==108",f"result['scratchSum']=={total}").replace('All 21 mathematical','All 39 mathematical')
script('compare_arithmetic_diamond_comparison_ownership_9007.py',s)
s=tr((p/'record_source_parabolic_diamond_comparison_8968.py').read_text(encoding='utf-8'))
s=re.sub(r'\b108\b',str(total),s);s=re.sub(r'== 21\b','== 39',s);s=re.sub(r'== 7\b','== 5',s)
s=s.replace('"incrementModules": 21','"incrementModules": 39').replace('"linterScopes": 21','"linterScopes": 39').replace('Seven declaration-value audits verify 113','Five declaration-value audits verify 172').replace('int(a[2]) == 26323','int(a[2]) == 26415').replace('Dubon Parabolic Character and Diamond Reuse Assessment 2026-10-28.md',report)
s=s.replace('PARABOLIC DIAMOND COMPARISON','ARITHMETIC DIAMOND COMPARISON').replace('original parabolic congruence, explicitly conditional finite Gamma1 descent and native/period diamonds','original arithmetic diamond, Galois and homogeneous coefficient comparison')
script('record_source_arithmetic_diamond_comparison_9007.py',s)
for prefix in ['build','verify']:script(prefix+'_arithmetic_diamond_comparison_9007.ps1',tr((p/(prefix+'_parabolic_diamond_comparison_8968.ps1')).read_text(encoding='utf-8')))
s=tr((p/'archive_parabolic_diamond_comparison_canonical_8968.py').read_text(encoding='utf-8'))
s=s.replace('original parabolic operator congruence away from a fixed integer, actual finite parabolic/Tate word kernels and explicitly conditional transfer descent','original arithmetic field/Picard/period/Tate diamond, exact homogeneous coefficient convention and Galois compatibility')
script('archive_arithmetic_diamond_comparison_canonical_9007.py',s)
s=tr((p/'preflight_parabolic_diamond_comparison_8968.py').read_text(encoding='utf-8'))
s=s.replace("==21 and len(ns['queries'])==61 and ns['count']==108",f"==39 and len(ns['queries'])==111 and ns['count']=={total}").replace('modules=21,queries=61,exhaustiveScratchChecks=108,proofValueChecks=113',f'modules=39,queries=111,exhaustiveScratchChecks={total},proofValueChecks=172')
script('preflight_arithmetic_diamond_comparison_9007.py',s)
output('source-arithmetic-diamond-comparison-scratch-ownership-9007.json',json.dumps(owners,indent=2)+'\n')
output('arithmetic-diamond-comparison-preexecution-review-9007.json',json.dumps(dict(status='Prepared only. Integration requires predecessor canonical PASS and archive.',modules=39,queries=111,theorems=92,constructions=19,exhaustiveScratchChecks=total,proofValueChecks=172,scopes=5,receipts=digests,expectedConsumers=26415,expectedConstructions=2801,fullGoal=boundary,scripts=[dict(path=str(p/n),sha256=sha(p/n)) for n in scripts],productionMutation=False),indent=2)+'\n')
print(json.dumps(dict(scripts=len(scripts),modules=39,checks=total,proofEdges=172,productionMutation=False)))
