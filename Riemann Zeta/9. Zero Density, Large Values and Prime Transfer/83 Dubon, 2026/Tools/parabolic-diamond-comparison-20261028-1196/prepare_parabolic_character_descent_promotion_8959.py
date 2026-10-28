from pathlib import Path
from datetime import datetime,timezone
import json,re,hashlib,ast
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
stems=['source-primitive-parabolic-kernel-1','source-integral-saturation-1','source-supported-parabolic-congruence-1b','source-gamma-one-parabolic-descent-1']
names=[s+'-scratch-receipt.json' for s in stems]
certs=[json.loads((p/n).read_text(encoding='utf-8')) for n in names]
assert tuple(sum(len(c[k]) for c in certs) for k in ['modules','queries','theoremRegistrations','constructionRegistrations'])==(12,24,19,5)
total=sum(c['exhaustiveTheorems'] for c in certs);edges=sum(c['requiredProofValueEdges'] for c in certs)
assert (total,edges)==(35,55)
digests={n:sha(p/n) for n in names}
dependency='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> arithmetic realization of original finite Gamma1 homogeneous-coefficient Hecke characters -> finite parabolic character descent -> original character support, integral Hecke-span saturation, actual parabolic operator congruence and exact geometric transfer preimages.'
discharged='The already constructed original complex and Fourier-field H1 characters annihilate every operator zero on original integral parabolic H1. The actual integral Hecke span of those classes is finite and supports the same original character. Native finite-module support, a nonzero character fiber and a fixed torsion annihilator prove integrality of the original character value divided by every nonzero modulus coprime to one fixed nonzero integer when the operator vanishes after reduction on integral parabolic H1. Consequently the same compatible adic character kills such operators at every positive power of every prime away from that integer, uniformly in field and embedding. The literal finite Gamma1 parabolic operator ring is finite. Its zero-word relations equal those of the independently defined arithmetic Picard Tate-dual action. Assuming explicitly that each reduced original integral parabolic class has a parabolic preimage under the existing native transfer, the same whole original adic character descends to that actual finite operator ring.'
boundary='The geometric lifting condition sourceGammaOneIntegralParabolicTransfer is stated and remains unproved. The finite-character descent theorem is conditional on that precise transfer input and excludes the primes dividing the proved fixed nonzero integer. Neither full-H1 transfer surjectivity nor restriction landing in parabolic H1 discharges it. The already proved all-prime full-H1 character family remains unchanged. Exceptional primes, diamonds, coefficient-field/Frobenius/inertia realization, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain. Finite characters do not supply a characteristic-zero lift.16/20; DUB-17--20 OPEN; all twenty acceptance gates unchanged.'
route='Reuse the October 28 nine-repository refresh and the targeted public parabolic-Shapiro/finite-field comparison check. Native support, finite torsion annihilators, the existing original Fourier-character kernel and Hecke-word maps give the shorter integral Hecke-span route. It avoids general integral parabolic corestriction stability, a new unipotent cokernel classification, and a transient finite tensor algebra on that span. The separately audited direct parabolic reduction-kernel theorem is deferred as unnecessary for this route. The public complex-coefficient Shapiro entry displays a statement, not its accepted proof body, and does not prove the finite-coefficient counit lifting required here. Frozen mathematical bodies are promoted by import qualification only.'
status='The twelve-module original parabolic congruence and conditional finite Gamma1 descent scope passes 24 public axiom queries, 35 exhaustive scratch theorem checks, sixteen linters per module and four declaration-value audits with 55 required dependency checks, with zero diagnostics. Production aggregate, focused audits and sequential foundation/paper verification of the 8,959-module scope are pending.'
report='Dubon Parabolic Character Descent Reuse Assessment 2026-10-28.md'
routefile='parabolic-character-descent-promotion-route-1183.json'
def output(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output(report,'# Dubon original parabolic character congruence and descent assessment — 28 October 2026\n\n'+discharged+'\n\n'+dependency+'\n\n'+route+'\n\n'+status+'\n\n'+boundary+'\n\nThe [nine-repository refresh](Dubon%20Reuse%20Refresh%202026-10-28.md) records fixed revisions. The targeted follow-up, source hashes, exact limitations and route decisions are archived in `Tools/parabolic-character-descent-20261028-1183/parabolic-shapiro-reuse-1182/assessment.md.txt`. SourceParabolicReductionKernel is retained only as deferred scratch evidence. Root pins, the frozen paper and the owner-only synchronization BAT are unchanged.\n')
output(routefile,json.dumps(dict(recordedUTC=datetime.now(timezone.utc).isoformat(),dependency=dependency,discharged=discharged,remaining=boundary,route=route,receipts=digests,modules=12,queries=24,exhaustiveScratchChecks=35,proofValueChecks=55,productionMutation=False),indent=2)+'\n')
def tr(s):
 for a,b in [('GammaOneHomogeneousParabolic','ParabolicCharacterDescent'),('gamma_one_homogeneous_parabolic','parabolic_character_descent'),('gamma-one-homogeneous-parabolic','parabolic-character-descent'),('GammaOneArithmeticTateH1','GammaOneHomogeneousParabolic'),('gamma_one_arithmetic_tate_h1','gamma_one_homogeneous_parabolic'),('gamma-one-arithmetic-tate-h1','gamma-one-homogeneous-parabolic'),('8947','8959'),('8923','8947'),('8,947','8,959'),('8,923','8,947'),('20261028-1163','20261028-1183'),('20261027-1132','20261028-1163')]:s=s.replace(a,b)
 return s
s=tr((p/'integrate_source_gamma_one_homogeneous_parabolic_8947.py').read_text(encoding='utf-8'))
s=re.sub(r'^digests = .+$',lambda _:'digests = '+repr(digests),s,flags=re.M)
s=s.replace('(24, 24, 64, 52, 12)','(12, 12, 24, 19, 5)').replace('assert count == 151','assert count == 35').replace('"increment": 24, "queries": 64','"increment": 12, "queries": 24')
for key,val in [('dependency',dependency),('discharged',discharged),('boundary',boundary),('route',route),('status',status)]:s=re.sub(r'^'+key+r' = .+$',lambda _,key=key,val=val:key+' = '+repr(val),s,flags=re.M)
s=s.replace('Actual original homogeneous Gamma1 Tate H1 and parabolic source comparison','Original parabolic operator congruence and conditional finite Gamma1 character descent')
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
pattern=r'(?<!\d)(?:'+'|'.join(str(i) for i in range(1165,1184))+r')[a-z]?(?!\d)'
for f in p.iterdir():
 if f.is_file() and f.suffix in ['.json','.py','.ps1','.txt','.log','.exit','.lean'] and re.search(pattern,f.name):evidence.append(f.name)
# Preserve the deferred original-parabolic reduction theorem and every audit, without promoting it.
for f in p.iterdir():
 if f.is_file() and (f.name.startswith('SourceParabolicReductionKernel') or f.name.startswith('source-parabolic-reduction-kernel')) and f.suffix in ['.json','.lean','.log','.exit']:evidence.append(f.name)
for n in owners:evidence += [n+e for e in ['.lean','.log','.exit']]
folders=[f.name for f in p.iterdir() if f.is_dir() and re.search(pattern+r'$',f.name)]
for n in evidence+folders:assert(p/n).exists(),n
a=s.index('evidence=[p/');b=s.index("for cert in certs:\n    evidence.append",a)
s=s[:a]+'evidence=[p/'+repr(routefile)+']\nevidence += [p/n for n in '+repr(sorted(set(evidence)))+']\nfor folder in '+repr(folders)+':\n    evidence += sorted(f for f in (p/folder).rglob("*") if f.is_file())\n'+s[b:]
s=s.replace('parabolic-character-descent-promotion-route-1163.json',routefile)
s=s.replace("p / 'Dubon Homogeneous Integral Parabolic Reuse Assessment 2026-10-28.md'","p / "+repr(report))
s=re.sub(r"assert sha\(reportSource\) == '[A-F0-9]+'",lambda _:"assert sha(reportSource) == "+repr(sha(p/report)),s)
oldedge=next(x for x in (r/'Dubon Architecture.md').read_text(encoding='utf-8').splitlines() if x.startswith('  GAMMAONEHOMOGPARAB8947['))
newedge='  GAMMAONEHOMOGPARAB8947["Original homogeneous arithmetic Tate dual/parabolic H1, whole Hecke words, nonzero original parabolic eigenclass and integral span proved (DUB-17/18)"] --> PARABCHAR8959\n  PARABCHAR8959["Original parabolic operator congruences at all precisions away from one fixed integer proved; actual finite parabolic/Tate word kernels identified. Character descent CONDITIONAL on exact parabolic transfer preimages. Exceptions, diamonds, Galois realization and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
s=re.sub(r'^edge = .+$',lambda _:'edge = '+repr(oldedge),s,flags=re.M)
s=re.sub(r'^arch.write_text\(.*$',lambda _:"arch.write_text(arch.read_text(encoding='utf-8').replace(edge,"+repr(newedge)+"),encoding='utf-8')",s,flags=re.M)
a=s.index("b = re.sub('  logInfo");b=s.index(', b)',a)+len(', b)')
line='  logInfo m!"SOURCE PARABOLIC CHARACTER DESCENT AUDIT PASS: {count} theorems including private/generated declarations. Original parabolic congruence away from a fixed integer, actual finite parabolic/Tate word kernel, and explicitly conditional transfer descent. Geometric lifting, exceptional primes, diamonds and all-weight association remain;16/20 gates."\n'
s=s[:a]+'b = re.sub('+repr('  logInfo m!".*"\\n')+', '+repr(line)+', b)'+s[b:]
scripts=[]
def script(n,s):
 if n.endswith('.py'):ast.parse(s)
 output(n,s);scripts.append(n)
script('integrate_source_parabolic_character_descent_8959.py',s)
for n in ['prepare_gamma_one_homogeneous_parabolic_production_ownership_8947.py','prepare_gamma_one_homogeneous_parabolic_global_ownership_8947.py']:script(tr(n),tr((p/n).read_text(encoding='utf-8')))
s=tr((p/'compare_gamma_one_homogeneous_parabolic_ownership_8947.py').read_text(encoding='utf-8'))
s=s.replace('==24','==12').replace('==5','==4').replace("result['scratchSum']==151","result['scratchSum']==35").replace('All 24 mathematical','All 12 mathematical')
script('compare_parabolic_character_descent_ownership_8959.py',s)
s=tr((p/'record_source_gamma_one_homogeneous_parabolic_8947.py').read_text(encoding='utf-8'))
s=re.sub(r'\b151\b','35',s);s=re.sub(r'== 24\b','== 12',s);s=re.sub(r'== 5\b','== 4',s)
s=s.replace('"incrementModules": 24','"incrementModules": 12').replace('"linterScopes": 24','"linterScopes": 12').replace('Five declaration-value audits verify 99','Four declaration-value audits verify 55').replace('int(a[2]) == 26277','int(a[2]) == 26296').replace('Dubon Homogeneous Integral Parabolic Reuse Assessment 2026-10-28.md',report)
s=s.replace('GAMMA ONE HOMOGENEOUS PARABOLIC','PARABOLIC CHARACTER DESCENT').replace('actual original homogeneous Gamma1 Tate H1 and parabolic source comparison','original parabolic congruence and explicitly conditional finite Gamma1 descent')
script('record_source_parabolic_character_descent_8959.py',s)
for prefix in ['build','verify']:script(prefix+'_parabolic_character_descent_8959.ps1',tr((p/(prefix+'_gamma_one_homogeneous_parabolic_8947.ps1')).read_text(encoding='utf-8')))
s=tr((p/'archive_gamma_one_homogeneous_parabolic_canonical_8947.py').read_text(encoding='utf-8'))
s=s.replace('actual original homogeneous Gamma1 Tate dual/parabolic H1 and whole-word comparison, original nonzero parabolic eigenclass, integral parabolic span and integral operator relations','original parabolic operator congruence away from a fixed integer, actual finite parabolic/Tate word kernels and explicitly conditional transfer descent')
script('archive_parabolic_character_descent_canonical_8959.py',s)
s=tr((p/'preflight_gamma_one_homogeneous_parabolic_8947.py').read_text(encoding='utf-8'))
s=s.replace("==24 and len(ns['queries'])==64 and ns['count']==151","==12 and len(ns['queries'])==24 and ns['count']==35").replace('modules=24,queries=64,exhaustiveScratchChecks=151,proofValueChecks=99','modules=12,queries=24,exhaustiveScratchChecks=35,proofValueChecks=55')
script('preflight_parabolic_character_descent_8959.py',s)
output('source-parabolic-character-descent-scratch-ownership-8959.json',json.dumps(owners,indent=2)+'\n')
output('parabolic-character-descent-preexecution-review-8959.json',json.dumps(dict(status='Prepared only. Integration requires predecessor canonical PASS and archive.',modules=12,queries=24,theorems=19,constructions=5,exhaustiveScratchChecks=35,proofValueChecks=55,scopes=4,receipts=digests,expectedConsumers=26296,expectedConstructions=2772,fullGoal=boundary,deferred=['SourceParabolicReductionKernel'],scripts=[dict(path=str(p/n),sha256=sha(p/n)) for n in scripts],productionMutation=False),indent=2)+'\n')
print(json.dumps(dict(scripts=len(scripts),modules=12,checks=35,proofEdges=55,productionMutation=False)))
