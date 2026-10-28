from pathlib import Path
from datetime import datetime,timezone
import json,re,hashlib,ast
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
stems=['source-gamma-one-binary-tate-h1-1','source-original-parabolic-entry-1b','source-parabolic-rational-span-1','source-original-integral-parabolic-1','source-primitive-parabolic-relation-1']
names=[s+'-scratch-receipt.json' for s in stems]
certs=[json.loads((p/n).read_text(encoding='utf-8')) for n in names]
assert tuple(sum(len(c[k]) for c in certs) for k in ['modules','queries','theoremRegistrations','constructionRegistrations'])==(24,64,52,12)
total=sum(c['exhaustiveTheorems'] for c in certs);edges=sum(c['requiredProofValueEdges'] for c in certs)
assert (total,edges)==(151,99)
digests={n:sha(p/n) for n in names}
dependency='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> arithmetic realization of original finite Gamma1 homogeneous-coefficient Hecke characters -> finite parabolic character descent and actual arithmetic Tate comparison -> original homogeneous coefficients, whole Hecke words, original nonzero parabolic eigenclass, integral parabolic span and integral operator relations.'
discharged='The actual arithmetic Gamma1 Picard Tate module dual with the original homogeneous polynomial coefficients is equivalent to the literal native parabolic H1 at Q*(p^(n+1))^2 for p>3. Finite-order vanishing follows from the existing trace bound and actual level congruences. Independently defined arithmetic Picard Hecke duals followed by the original homogeneous matrix action intertwine every original prime operator and integral Hecke word. The original primitive period class is nonzero in parabolic homogeneous-coefficient H1 with the original eigenvalues. Coefficient reduction preserves local coboundaries; the literal diagonal Gamma1 restriction sends them to zero. Rational coordinates preserve the actual whole-cusp-stabilizer witnesses. The already finite original cusp quotient and native cocycle denominator give one uniform integer clearing the cocycle and all representative witnesses; integral conjugation transports them to every cusp. Thus the original period class lies in the complex span of actual integral parabolic H1. The original Fourier character annihilates every integral Hecke word vanishing on that submodule, without assuming vanishing on full H1.'
boundary='The original finite character still acts on full H1; its descent to the finite parabolic operator image and the required finite congruence/saturation remain unproved. Integral parabolic spanning and characteristic-zero operator relations do not establish finite descent. Restriction landing in parabolic H1 does not assert nonvanishing or surjectivity. Diamonds, coefficient-field/Frobenius/inertia realization, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain. Finite characters do not supply a characteristic-zero lift. 16/20; DUB-17--20 OPEN; all twenty acceptance gates unchanged.'
route='Reuse the October 28 fixed-revision nine-repository search and the existing native monomial basis, scalar period-lattice duality, IsBaseChange, arithmetic Picard Hecke and Hecke-word transport. The original cusp-period witness survives coefficient morphisms and rational projection. Finitely many actual cusp-orbit representatives permit uniform integral denominator clearing; the native cocycle conjugation identity transports witnesses. This avoids a new cusp-width classification, polynomial or tensor basis, and a general parabolic corestriction theory. Native finite-generator reconstruction and H1 quotient maps give the source integral span. The existing word intertwiner and actual eigenclass evaluate the integral parabolic relation directly. New TauCeti diamond/modular-curve results remain bounded research candidates, not imported proof closures. Frozen mathematical bodies are promoted by import qualification only.'
status='The twenty-four-module homogeneous Tate/H1 and original integral parabolic source comparison passes 64 public axiom queries, 151 exhaustive scratch theorem checks, sixteen linters per module and five declaration-value audits with 99 required dependency checks, with zero diagnostics. Production aggregate, focused audits and sequential foundation/paper verification of the 8,947-module scope are pending.'
report='Dubon Homogeneous Integral Parabolic Reuse Assessment 2026-10-28.md'
routefile='gamma-one-homogeneous-parabolic-promotion-route-1163.json'
def output(n,t):
 f=p/n;assert not f.exists(),f
 f.write_text(t,encoding='utf-8')
output(report,'# Dubon original homogeneous Tate/H1 and parabolic source reuse assessment - 28 October 2026\n\n'+discharged+'\n\n'+dependency+'\n\n'+route+'\n\n'+status+'\n\n'+boundary+'\n\nThe [nine-repository live search](Dubon%20Reuse%20Refresh%202026-10-28.md) records fixed revisions and bounded coverage. This assessment records local adaptations, not an external complete import-closure build. Root pins, the frozen paper and the owner-only synchronization BAT are unchanged.\n')
output(routefile,json.dumps(dict(recordedUTC=datetime.now(timezone.utc).isoformat(),dependency=dependency,discharged=discharged,remaining=boundary,route=route,receipts=digests,modules=24,queries=64,exhaustiveScratchChecks=total,proofValueChecks=edges,productionMutation=False),indent=2)+'\n')
def tr(s):
 for a,b in [('GammaOneArithmeticTateH1','GammaOneHomogeneousParabolic'),('gamma_one_arithmetic_tate_h1','gamma_one_homogeneous_parabolic'),('gamma-one-arithmetic-tate-h1','gamma-one-homogeneous-parabolic'),('GammaOnePicardHeckeComparison','GammaOneArithmeticTateH1'),('gamma_one_picard_hecke_comparison','gamma_one_arithmetic_tate_h1'),('gamma-one-picard-hecke-comparison','gamma-one-arithmetic-tate-h1'),('8923','8947'),('8867','8923'),('8,923','8,947'),('8,867','8,923'),('20261027-1132','20261028-1163'),('20261027-1070','20261027-1132')]:s=s.replace(a,b)
 return s
s=tr((p/'integrate_source_gamma_one_arithmetic_tate_h1_8923.py').read_text(encoding='utf-8'))
s=re.sub(r'^digests = .+$',lambda _:'digests = '+repr(digests),s,flags=re.M)
s=s.replace('(56, 56, 178, 140, 38)','(24, 24, 64, 52, 12)').replace('assert count == 357','assert count == 151').replace('"increment": 56, "queries": 178','"increment": 24, "queries": 64')
for k,v in [('dependency',dependency),('discharged',discharged),('boundary',boundary),('route',route),('status',status)]:s=re.sub(r'^'+k+r' = .+$',lambda _,k=k,v=v:k+' = '+repr(v),s,flags=re.M)
s=s.replace('Actual original Gamma1 arithmetic Tate and finite H1 comparison','Actual original homogeneous Gamma1 Tate H1 and parabolic source comparison')
evidence=list(names)+[n+'-audit-config.json' for n in stems]
owners=[Path(c['ownershipLog']).stem for c in certs]
for c in certs:
 for k in ['log','dependencyAuditLog']:
  f=Path(c[k]);evidence += [f.with_suffix(e).name for e in ['.lean','.log','.exit']]
 for row in c['files']:evidence += [Path(row['path']).name,Path(row['compileLog']).name,Path(row['compileExit']).name]
 evidence.append(Path(c['reuseReview']).name)
 rv=json.loads(Path(c['reuseReview']).read_text(encoding='utf-8'));rf=Path(rv['routeAssessment']['path']);evidence.append(rf.name)
 rd=json.loads(rf.read_text(encoding='utf-8'))
 for row in rd.get('reuseChecked',[]):
  f=Path(row['path'])
  if f.is_relative_to(p):evidence.append(str(f.relative_to(p)))
pattern=r'(?<!\d)(?:'+'|'.join(str(i) for i in range(1133,1164))+r')[a-z]?(?!\d)'
for f in p.iterdir():
 if f.is_file() and f.suffix in ['.json','.py','.ps1','.txt','.log','.exit','.lean'] and re.search(pattern,f.name):evidence.append(f.name)
for n in owners:evidence += [n+e for e in ['.lean','.log','.exit']]
folders=[f.name for f in p.iterdir() if f.is_dir() and re.search(pattern+r'$',f.name)]
for n in evidence+folders:assert(p/n).exists(),n
a=s.index('evidence=[p/');b=s.index("for cert in certs:\n    evidence.append",a)
s=s[:a]+'evidence=[p/'+repr(routefile)+']\nevidence += [p/n for n in '+repr(sorted(set(evidence)))+']\nfor folder in '+repr(folders)+':\n    evidence += sorted(f for f in (p/folder).rglob("*") if f.is_file())\n'+s[b:]
s=s.replace('gamma-one-homogeneous-parabolic-promotion-route-1132.json',routefile)
s=s.replace("p / 'Dubon Arithmetic Tate H1 Reuse Assessment 2026-10-27.md'","p / "+repr(report))
s=re.sub(r"assert sha\(reportSource\) == '[A-F0-9]+'",lambda _:"assert sha(reportSource) == "+repr(sha(p/report)),s)
oldedge=next(x for x in (r/'Dubon Architecture.md').read_text(encoding='utf-8').splitlines() if x.startswith('  GAMMAONEARITHTATE8923['))
newedge='  GAMMAONEARITHTATE8923["Actual arithmetic Gamma1 Picard torsion descent, Tate-period and scalar finite H1 dual Hecke comparison proved (DUB-17/18)"] --> GAMMAONEHOMOGPARAB8947\n  GAMMAONEHOMOGPARAB8947["Original homogeneous arithmetic Tate dual/parabolic H1 and whole Hecke words proved; original nonzero parabolic eigenclass, integral span and integral operator relations proved. Finite character descent, diamonds, Galois realization and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
s=re.sub(r'^edge = .+$',lambda _:'edge = '+repr(oldedge),s,flags=re.M)
s=re.sub(r'^arch.write_text\(.*$',lambda _:"arch.write_text(arch.read_text(encoding='utf-8').replace(edge,"+repr(newedge)+"),encoding='utf-8')",s,flags=re.M)
a=s.index("b = re.sub('  logInfo");b=s.index(', b)',a)+len(', b)')
line='  logInfo m!"SOURCE GAMMA ONE HOMOGENEOUS PARABOLIC AUDIT PASS: {count} theorems including private/generated declarations. Actual homogeneous Tate dual/parabolic H1 and original whole Hecke words, original parabolic eigenclass, integral span and integral operator relations. Finite character descent, diamonds and all-weight association remain; 16/20 gates."\n'
s=s[:a]+'b = re.sub('+repr('  logInfo m!".*"\\n')+', '+repr(line)+', b)'+s[b:]
scripts=[]
def script(n,t):
 if n.endswith('.py'):ast.parse(t)
 output(n,t);scripts.append(n)
script('integrate_source_gamma_one_homogeneous_parabolic_8947.py',s)
for n in ['prepare_gamma_one_arithmetic_tate_h1_production_ownership_8923.py','prepare_gamma_one_arithmetic_tate_h1_global_ownership_8923.py']:script(tr(n),tr((p/n).read_text(encoding='utf-8')))
s=tr((p/'compare_gamma_one_arithmetic_tate_h1_ownership_8923.py').read_text(encoding='utf-8'))
s=s.replace('==56','==24').replace('==6','==5').replace("result['scratchSum']==357","result['scratchSum']==151").replace('All 56 mathematical','All 24 mathematical')
script('compare_gamma_one_homogeneous_parabolic_ownership_8947.py',s)
s=tr((p/'record_source_gamma_one_arithmetic_tate_h1_8923.py').read_text(encoding='utf-8'))
s=re.sub(r'\b357\b','151',s);s=re.sub(r'== 56\b','== 24',s);s=re.sub(r'== 6\b','== 5',s)
s=s.replace('"incrementModules": 56','"incrementModules": 24').replace('"linterScopes": 56','"linterScopes": 24').replace('Six declaration-value audits verify 207','Five declaration-value audits verify 99').replace('int(a[2]) == 26225','int(a[2]) == 26277').replace('Dubon Arithmetic Tate H1 Reuse Assessment 2026-10-27.md',report)
s=s.replace('GAMMA ONE ARITHMETIC TATE H1','GAMMA ONE HOMOGENEOUS PARABOLIC').replace('actual original Gamma1 arithmetic Tate and finite H1 comparison','actual original homogeneous Gamma1 Tate H1 and parabolic source comparison')
script('record_source_gamma_one_homogeneous_parabolic_8947.py',s)
for prefix in ['build','verify']:script(prefix+'_gamma_one_homogeneous_parabolic_8947.ps1',tr((p/(prefix+'_gamma_one_arithmetic_tate_h1_8923.ps1')).read_text(encoding='utf-8')))
s=tr((p/'archive_gamma_one_arithmetic_tate_h1_canonical_8923.py').read_text(encoding='utf-8'))
s=s.replace('actual original Gamma1 arithmetic torsion descent, Tate-period and finite H1 dual Hecke comparison with explicit parabolic and finite-order vanishing target','actual original homogeneous Gamma1 Tate dual/parabolic H1 and whole-word comparison, original nonzero parabolic eigenclass, integral parabolic span and integral operator relations')
script('archive_gamma_one_homogeneous_parabolic_canonical_8947.py',s)
s=tr((p/'preflight_gamma_one_arithmetic_tate_h1_8923.py').read_text(encoding='utf-8'))
s=s.replace("==56 and len(ns['queries'])==178 and ns['count']==357","==24 and len(ns['queries'])==64 and ns['count']==151")
s=s.replace('modules=56,queries=178,exhaustiveScratchChecks=357,proofValueChecks=207','modules=24,queries=64,exhaustiveScratchChecks=151,proofValueChecks=99')
script('preflight_gamma_one_homogeneous_parabolic_8947.py',s)
output('source-gamma-one-homogeneous-parabolic-scratch-ownership-8947.json',json.dumps(owners,indent=2)+'\n')
output('gamma-one-homogeneous-parabolic-preexecution-review-8947.json',json.dumps(dict(status='Prepared only. Integration requires predecessor canonical PASS and archive.',modules=24,queries=64,theorems=52,constructions=12,exhaustiveScratchChecks=total,proofValueChecks=edges,scopes=5,receipts=digests,expectedConsumers=26277,expectedConstructions=2767,fullGoal=boundary,scripts=[dict(path=str(p/n),sha256=sha(p/n)) for n in scripts],productionMutation=False),indent=2)+'\n')
print(json.dumps(dict(scripts=len(scripts),modules=24,checks=total,proofEdges=edges,productionMutation=False)))
