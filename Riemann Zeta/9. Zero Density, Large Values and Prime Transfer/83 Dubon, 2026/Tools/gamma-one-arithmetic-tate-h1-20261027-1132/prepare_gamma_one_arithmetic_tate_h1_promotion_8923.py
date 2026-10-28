from pathlib import Path
from datetime import datetime, timezone
import json,re,hashlib,ast
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
stems=['source-gamma-one-real-parabolic-hecke-1','source-gamma-one-complex-tate-hecke-1','source-gamma-one-arithmetic-picard-injectivity-1','source-gamma-one-arithmetic-torsion-tate-1b','source-gamma-one-arithmetic-hecke-1','source-gamma-one-finite-tate-h1-1b']
names=[s+'-scratch-receipt.json' for s in stems]
certs=[json.loads((p/n).read_text(encoding='utf-8')) for n in names]
assert tuple(sum(len(c[k]) for c in certs) for k in ['modules','queries','theoremRegistrations','constructionRegistrations'])==(56,178,140,38)
total=sum(c['exhaustiveTheorems'] for c in certs)
edges=sum(c['requiredProofValueEdges'] for c in certs)
digests={n:sha(p/n) for n in names}
dependency='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> arithmetic realization of original finite Gamma1 homogeneous-coefficient Hecke characters -> full/parabolic, transpose, diamond and arithmetic Picard/H1 comparison -> actual finite arithmetic Tate dual and native H1 Hecke comparison.'
discharged='The actual arithmetic Gamma1 Picard group injects into the complex Picard group, and every nonzero-modulus complex torsion class descends. The resulting arithmetic-to-complex Tate equivalence preserves the actual Hecke operators. Its composition with the original Picard-period equivalence identifies the arithmetic Tate module with the p-adic tensor of the original finite free integral-period lattice. Prime Hecke operators act by the actual dual cusp operator, including primes dividing the level. Integer parabolic characters factor through that lattice by the proved real-period surjectivity. The proved integral lift gives an equivalence between its modulus dual and the literal native H1 submodule whose characters vanish on parabolic and finite-order elements. Native base-change universality identifies this same H1 submodule with finite characters of the actual arithmetic Tate module. This equivalence intertwines arithmetic Picard prime Hecke duals and native H1 Hecke operators. The real parabolic H1 comparison and stability are also proved. No arithmetic torsion descent, Tate comparison, lattice-dual realization or Hecke compatibility premise remains in these stated comparisons.'
boundary='The finite H1 target explicitly retains parabolic and finite-order vanishing. The full/parabolic passage, discharge of finite-order vanishing for the application, original homogeneous coefficients and diamonds, coefficient-field/Frobenius/inertia realization, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain. No rank-equals-twice-genus claim is inferred from the lattice-rank torsion cardinality. Finite characters do not supply a characteristic-zero lift. 16/20; DUB-17--20 OPEN; all twenty acceptance gates unchanged.'
route='Reuse the fixed-revision October 27 search and proved local arithmetic curves, constant-field places, finite Riemann-Roch spaces, period surjectivity, integral character lifting and native tensor universal properties. Coefficient-span descent and equality of coordinate degrees prove Picard injectivity; finite torsion actions and translation orbits prove torsion descent. Only place extension and divisor conorm are developed for the Hecke intersection field. The finite H1 route factors integer characters through the actual period kernel and uses the existing integral lift, avoiding a second integral Poincare-duality argument. IsBaseChange from the proved arithmetic Tate equivalence avoids a new tensor basis construction. Frozen mathematical bodies are promoted by import qualification only.'
status=f'The fifty-six-module arithmetic Tate and finite H1 comparison passes 178 public axiom queries, {total} exhaustive scratch theorem checks, sixteen linters per module and six declaration-value audits with {edges} required dependency checks, with zero diagnostics. Production aggregate, focused audits and sequential foundation/paper verification of the 8,923-module scope are pending.'
report='Dubon Arithmetic Tate H1 Reuse Assessment 2026-10-27.md'
archive='Tools/gamma-one-arithmetic-tate-h1-20261027-1132'
routefile='gamma-one-arithmetic-tate-h1-promotion-route-1132.json'
def output(n,t):
 f=p/n;assert not f.exists(),f
 f.write_text(t,encoding='utf-8')
output(report,'# Dubon actual arithmetic Tate and finite H1 reuse assessment - 27 October 2026\n\n'+discharged+'\n\n'+dependency+'\n\n'+route+'\n\n'+status+'\n\n'+boundary+'\n\nThe [seven-head live search](Dubon%20Reuse%20Refresh%202026-10-27.md) records fixed revisions and bounded coverage. This assessment records the subsequent local adaptations, not an external complete import-closure build. Root pins, the frozen paper and the owner-only synchronization BAT are unchanged.\n')
output(routefile,json.dumps(dict(recordedUTC=datetime.now(timezone.utc).isoformat(),dependency=dependency,discharged=discharged,remaining=boundary,route=route,receipts=digests,modules=56,queries=178,exhaustiveScratchChecks=total,proofValueChecks=edges,productionMutation=False),indent=2)+'\n')
def tr(s):
 for a,b in [('GammaOnePicardHeckeComparison','GammaOneArithmeticTateH1'),('gamma_one_picard_hecke_comparison','gamma_one_arithmetic_tate_h1'),('gamma-one-picard-hecke-comparison','gamma-one-arithmetic-tate-h1'),('GammaOnePrincipalDivisor','GammaOnePicardHeckeComparison'),('gamma_one_principal_divisor','gamma_one_picard_hecke_comparison'),('gamma-one-principal-divisor','gamma-one-picard-hecke-comparison'),('8867','8923'),('8821','8867'),('8,867','8,923'),('8,821','8,867'),('20261027-1070','20261027-1132'),('20261027-1015','20261027-1070')]:s=s.replace(a,b)
 return s
s=tr((p/'integrate_source_gamma_one_picard_hecke_comparison_8867b.py').read_text(encoding='utf-8'))
s=s.replace('paper-verification-8867b-console','paper-verification-8867-console')
s=re.sub(r'^digests = .+$',lambda _: 'digests = '+repr(digests),s,flags=re.M)
s=s.replace('(46, 46, 128, 100, 28)','(56, 56, 178, 140, 38)')
s=s.replace('assert count == 216','assert count == '+str(total)).replace('"increment": 46, "queries": 128','"increment": 56, "queries": 178')
for k,v in [('dependency',dependency),('discharged',discharged),('boundary',boundary),('route',route),('status',status)]:s=re.sub(r'^'+k+r' = .+$',lambda _,k=k,v=v:k+' = '+repr(v),s,flags=re.M)
s=s.replace('Actual original Gamma1 Picard and Hecke comparison','Actual original Gamma1 arithmetic Tate and finite H1 comparison')
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
pattern=r'(?<!\d)(?:'+'|'.join(str(i) for i in range(1071,1133))+r')[a-z]?(?!\d)'
for f in p.iterdir():
 if f.is_file() and f.suffix in ['.json','.py','.ps1','.txt','.log','.exit','.lean'] and re.search(pattern,f.name):evidence.append(f.name)
for n in owners:evidence += [n+e for e in ['.lean','.log','.exit']]
folders=[f.name for f in p.iterdir() if f.is_dir() and re.search(pattern+r'$',f.name)]
for n in evidence+folders:assert(p/n).exists(),n
a=s.index('evidence=[p/');b=s.index("for cert in certs:\n    evidence.append",a)
s=s[:a]+'evidence=[p/'+repr(routefile)+']\nevidence += [p/n for n in '+repr(sorted(set(evidence)))+']\nfor folder in '+repr(folders)+':\n    evidence += sorted(f for f in (p/folder).rglob("*") if f.is_file())\n'+s[b:]
s=s.replace('gamma-one-arithmetic-tate-h1-promotion-route-1070.json',routefile)
s=s.replace("p / 'Dubon Picard Hecke Reuse Assessment 2026-10-27.md'","p / "+repr(report))
s=re.sub(r"assert sha\(reportSource\) == '[A-F0-9]+'",lambda _:"assert sha(reportSource) == "+repr(sha(p/report)),s)
oldedge=next(x for x in (r/'Dubon Architecture.md').read_text(encoding='utf-8').splitlines() if x.startswith('  GAMMAONEPICARDHECKE8867['))
newedge='  GAMMAONEPICARDHECKE8867["Actual complex Gamma1 Picard-period and prime Hecke comparison proved (DUB-17/18)"] --> GAMMAONEARITHTATE8923\n  GAMMAONEARITHTATE8923["Actual arithmetic Picard torsion descent, Tate-period and finite H1 dual Hecke comparison proved. H1 target retains parabolic and finite-order vanishing. Full/coefficient/diamond realization, all-weight association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
s=re.sub(r'^edge = .+$',lambda _:'edge = '+repr(oldedge),s,flags=re.M)
s=re.sub(r'^arch.write_text\(.*$',lambda _:"arch.write_text(arch.read_text(encoding='utf-8').replace(edge,"+repr(newedge)+"),encoding='utf-8')",s,flags=re.M)
a=s.index("b = re.sub('  logInfo");b=s.index(', b)',a)+len(', b)')
logline='  logInfo m!"SOURCE GAMMA ONE ARITHMETIC TATE H1 AUDIT PASS: {count} theorems including private/generated declarations. Actual arithmetic torsion descent, Tate-period and finite H1 dual Hecke comparison. Full/parabolic passage, homogeneous coefficients, diamonds and all-weight association remain; 16/20 gates."\n'
s=s[:a]+'b = re.sub('+repr('  logInfo m!".*"\\n')+', '+repr(logline)+', b)'+s[b:]
scripts=[]
def script(n,t):
 if n.endswith('.py'):ast.parse(t)
 output(n,t);scripts.append(n)
script('integrate_source_gamma_one_arithmetic_tate_h1_8923.py',s)
for n in ['prepare_gamma_one_picard_hecke_comparison_production_ownership_8867.py','prepare_gamma_one_picard_hecke_comparison_global_ownership_8867.py']:
 script(tr(n),tr((p/n).read_text(encoding='utf-8')))
s=tr((p/'compare_gamma_one_picard_hecke_comparison_ownership_8867.py').read_text(encoding='utf-8'))
s=s.replace('==46','==56').replace('==8','==6').replace("result['scratchSum']==216","result['scratchSum']=="+str(total)).replace('All 46 mathematical','All 56 mathematical')
script('compare_gamma_one_arithmetic_tate_h1_ownership_8923.py',s)
s=tr((p/'record_source_gamma_one_picard_hecke_comparison_8867.py').read_text(encoding='utf-8'))
s=re.sub(r'\b216\b',str(total),s);s=re.sub(r'== 46\b','== 56',s);s=re.sub(r'== 8\b','== 6',s)
s=s.replace('"incrementModules": 46','"incrementModules": 56').replace('"linterScopes": 46','"linterScopes": 56').replace('Eight declaration-value audits verify 189','Six declaration-value audits verify '+str(edges)).replace('int(a[2]) == 26085','int(a[2]) == 26225').replace('Dubon Picard Hecke Reuse Assessment 2026-10-27.md',report)
s=s.replace('GAMMA ONE PICARD HECKE COMPARISON','GAMMA ONE ARITHMETIC TATE H1').replace('actual original Gamma1 Picard and Hecke comparison','actual original Gamma1 arithmetic Tate and finite H1 comparison')
script('record_source_gamma_one_arithmetic_tate_h1_8923.py',s)
for prefix in ['build','verify']:
 script(prefix+'_gamma_one_arithmetic_tate_h1_8923.ps1',tr((p/(prefix+'_gamma_one_picard_hecke_comparison_8867.ps1')).read_text(encoding='utf-8')))
s=tr((p/'archive_gamma_one_picard_hecke_comparison_canonical_8867.py').read_text(encoding='utf-8'))
s=s.replace('actual original complex Gamma1 Picard-period equivalence and prime Hecke compatibility, plus native holomorphic H1 compatibility','actual original Gamma1 arithmetic torsion descent, Tate-period and finite H1 dual Hecke comparison with explicit parabolic and finite-order vanishing target')
script('archive_gamma_one_arithmetic_tate_h1_canonical_8923.py',s)
s=tr((p/'preflight_gamma_one_picard_hecke_comparison_8867b.py').read_text(encoding='utf-8'))
s=s.replace('8923b','8923').replace("==46 and len(ns['queries'])==128 and ns['count']==216","==56 and len(ns['queries'])==178 and ns['count']=="+str(total))
s=s.replace('modules=46,queries=128,exhaustiveScratchChecks=216,proofValueChecks=189',f'modules=56,queries=178,exhaustiveScratchChecks={total},proofValueChecks={edges}')
script('preflight_gamma_one_arithmetic_tate_h1_8923.py',s)
output('source-gamma-one-arithmetic-tate-h1-scratch-ownership-8923.json',json.dumps(owners,indent=2)+'\n')
output('gamma-one-arithmetic-tate-h1-preexecution-review-8923.json',json.dumps(dict(status='Prepared only. Integration requires predecessor canonical PASS and archive.',modules=56,queries=178,theorems=140,constructions=38,exhaustiveScratchChecks=total,proofValueChecks=edges,scopes=6,receipts=digests,expectedConsumers=26225,expectedConstructions=2755,fullGoal=boundary,scripts=[dict(path=str(p/n),sha256=sha(p/n)) for n in scripts],productionMutation=False),indent=2)+'\n')
print(json.dumps(dict(scripts=len(scripts),modules=56,checks=total,proofEdges=edges,productionMutation=False)))
