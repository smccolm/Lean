from pathlib import Path
from datetime import datetime, timezone
import json,re,hashlib,ast
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
stems=['source-gamma-one-analytic-abel-kernel-1','source-gamma-one-picard-period-equivalence-1d','source-gamma-one-hecke-analytic-maps-1','source-gamma-one-hecke-primitive-trace-1','source-gamma-one-holomorphic-h1-hecke-1','source-gamma-one-period-lattice-hecke-1b','source-gamma-one-hecke-geometric-fibers-1b','source-gamma-one-picard-period-hecke-1']
names=[s+'-scratch-receipt.json' for s in stems]
certs=[json.loads((p/n).read_text(encoding='utf-8')) for n in names]
assert tuple(sum(len(c[k]) for c in certs) for k in ['modules','queries','theoremRegistrations','constructionRegistrations'])==(46,128,100,28)
total=sum(c['exhaustiveTheorems'] for c in certs)
edges=sum(c['requiredProofValueEdges'] for c in certs)
assert edges==189
digests={n:sha(p/n) for n in names}
dependency='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> arithmetic realization of original finite Gamma1 homogeneous-coefficient Hecke characters -> full/parabolic, transpose, diamond and Picard/H1 comparison -> actual Picard-period equivalence and prime Hecke compatibility.'
discharged='The actual original complex Gamma1 Picard group is now identified with the original integer-period quotient by a proved additive equivalence. The forward Abel implication and finite Jacobi inversion discharge its kernel and surjectivity assumptions. The native holomorphic H1 period map intertwines the actual constant-coefficient Hecke operator for every nonzero index. The dual cusp trace preserves the original integer-period lattice. Actual intersection-curve orbit separation, exact ramification and coset multiplicity identify literal prime beta pullback followed by alpha pushforward with the analytic coset divisor sum, including elliptic fibers. The degree-zero hypothesis cancels the explicitly computed endpoint basepoint term. Consequently the original Picard-period equivalence intertwines the literal algebraic prime Hecke correspondence and the native dual cusp action, including primes dividing the level. No Picard equivalence, Hecke compatibility, fiber multiplicity, lattice stability or degree-zero cancellation certificate remains assumed in these complex comparisons.'
boundary='This proves the complex additive Picard-period and prime Hecke comparison and the holomorphic constant-coefficient H1 comparison. Full parabolic, diamond, transpose and arithmetic compatibility, coefficient-field transport, Frobenius/inertia, arithmetic realization of original finite homogeneous-coefficient Gamma1 characters, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain. Finite characters, complex semisimplicity, Witt coefficients and universal deformation rings do not supply a characteristic-zero lift. 16/20; DUB-17--20 OPEN; all twenty acceptance gates unchanged.'
route='Reuse the October 27 fixed-revision source assessment and the existing local foundations. Native endpoint primitives and Jacobi inversion, literal divisor pull/push, positive ramification-weight counting, exact coset stabilizer counting, native cusp traces and H1 cocycles provide the required chain. The short all-fiber route uses generic separation and exact field degree to force every positive ramification bound to equality. Additive Finsupp extensionality extends the point formula, and degree zero removes the basepoint term. No separate intersection-curve modular-form separation theory, general quotient atlas or incidental correspondence abstraction is introduced. All used and failed evidence is retained; frozen mathematical bodies are promoted by import qualification only.'
status=f'The forty-six-module actual Gamma1 Picard and Hecke comparison scope passes 128 public axiom queries, {total} exhaustive scratch theorem checks, sixteen linters per module and eight declaration-value audits with 189 required dependency checks, with zero diagnostics. Production aggregate, focused audits and sequential foundation/paper verification of the 8,867-module scope are pending.'
report='Dubon Picard Hecke Reuse Assessment 2026-10-27.md'
archive='Tools/gamma-one-picard-hecke-comparison-20261027-1070'
routefile='gamma-one-picard-hecke-comparison-promotion-route-1070.json'
def output(n,t):
 f=p/n;assert not f.exists(),f
 f.write_text(t,encoding='utf-8')
output(report,'# Dubon actual Picard and Hecke reuse assessment - 27 October 2026\n\n'+discharged+'\n\n'+dependency+'\n\n'+route+'\n\n'+status+'\n\n'+boundary+'\n\nThe seven-head live search is preserved in [Dubon Reuse Refresh 2026-10-27.md](Dubon%20Reuse%20Refresh%202026-10-27.md), with fixed revisions and bounded coverage. This assessment records the subsequent local adaptations; it does not claim an external complete import-closure build. Root pins, the frozen paper and the owner-only synchronization BAT are unchanged.\n')
output(routefile,json.dumps(dict(recordedUTC=datetime.now(timezone.utc).isoformat(),dependency=dependency,discharged=discharged,remaining=boundary,route=route,receipts=digests,modules=46,queries=128,exhaustiveScratchChecks=total,proofValueChecks=edges,productionMutation=False),indent=2)+'\n')
def tr(s):
 for a,b in [('GammaOnePrincipalDivisor','GammaOnePicardHeckeComparison'),('gamma_one_principal_divisor','gamma_one_picard_hecke_comparison'),('gamma-one-principal-divisor','gamma-one-picard-hecke-comparison'),('GammaOneDivisorReciprocity','GammaOnePrincipalDivisor'),('gamma_one_divisor_reciprocity','gamma_one_principal_divisor'),('gamma-one-divisor-reciprocity','gamma-one-principal-divisor'),('8821b','8867'),('8821','8867'),('8776','8821'),('8,821','8,867'),('8,776','8,821'),('20261027-1015','20261027-1070'),('20261027-951','20261027-1015')]:
  s=s.replace(a,b)
 return s
s=tr((p/'integrate_source_gamma_one_principal_divisor_8821.py').read_text(encoding='utf-8'))
s=s.replace('paper-verification-8821-console','paper-verification-8821b-console')
s=re.sub(r'^digests = .+$',lambda _: 'digests = '+repr(digests),s,flags=re.M)
s=s.replace('(45, 45, 242, 200, 42)','(46, 46, 128, 100, 28)')
s=s.replace('assert count == 376','assert count == '+str(total)).replace('"increment": 45, "queries": 242','"increment": 46, "queries": 128')
for k,v in [('dependency',dependency),('discharged',discharged),('boundary',boundary),('route',route),('status',status)]:
 s=re.sub(r'^'+k+r' = .+$',lambda _,k=k,v=v:k+' = '+repr(v),s,flags=re.M)
s=s.replace('Actual original Gamma1 finite-divisor converse','Actual original Gamma1 Picard and Hecke comparison')
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
pattern='(?:'+'|'.join(str(i) for i in range(1016,1071))+')'
for f in p.iterdir():
 if f.is_file() and f.suffix in ['.json','.py','.ps1','.txt','.log','.exit'] and re.search(r'(?<!\d)'+pattern+r'[a-z]?(?:\.|-)',f.name):evidence.append(f.name)
for n in owners:evidence += [n+e for e in ['.lean','.log','.exit']]
folders=[f.name for f in p.iterdir() if f.is_dir() and re.search(pattern+r'[a-z]?$',f.name)]
for n in evidence+folders:assert(p/n).exists(),n
a=s.index('evidence=[p/');b=s.index("for cert in certs:\n    evidence.append",a)
s=s[:a]+'evidence=[p/'+repr(routefile)+']\nevidence += [p/n for n in '+repr(sorted(set(evidence)))+']\nfor folder in '+repr(folders)+':\n    evidence += sorted(f for f in (p/folder).rglob("*") if f.is_file())\n'+s[b:]
s=s.replace("p / 'Dubon Principal Divisor Reuse Assessment 2026-10-27.md'","p / "+repr(report))
s=re.sub(r"assert sha\(reportSource\) == '[A-F0-9]+'",lambda _:"assert sha(reportSource) == "+repr(sha(p/report)),s)
oldedge=next(x for x in (r/'Dubon Architecture.md').read_text(encoding='utf-8').splitlines() if x.startswith('  GAMMAONEPRINCIPAL8821['))
newedge='  GAMMAONEPRINCIPAL8821["Actual Gamma1 finite-divisor principalness converse proved (DUB-17/18)"] --> GAMMAONEPICARDHECKE8867\n  GAMMAONEPICARDHECKE8867["Actual complex Picard-period equivalence, holomorphic H1 Hecke compatibility and literal prime Picard Hecke compatibility proved. Full parabolic, diamond, transpose, arithmetic, all-weight association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
s=re.sub(r'^edge = .+$',lambda _:'edge = '+repr(oldedge),s,flags=re.M)
s=re.sub(r'^arch.write_text\(.*$',lambda _:"arch.write_text(arch.read_text(encoding='utf-8').replace(edge,"+repr(newedge)+"),encoding='utf-8')",s,flags=re.M)
a=s.index("b = re.sub('  logInfo");b=s.index(', b)',a)+len(', b)')
logline='  logInfo m!"SOURCE GAMMA ONE PICARD HECKE COMPARISON AUDIT PASS: {count} theorems including private/generated declarations. Actual original complex Picard-period and prime Hecke compatibility, plus holomorphic H1 Hecke compatibility. Full parabolic/diamond/transpose/arithmetic and all-weight association remain; 16/20 gates."\n'
s=s[:a]+'b = re.sub('+repr('  logInfo m!".*"\\n')+', '+repr(logline)+', b)'+s[b:]
scripts=[]
def script(n,t):
 if n.endswith('.py'):ast.parse(t)
 output(n,t);scripts.append(n)
script('integrate_source_gamma_one_picard_hecke_comparison_8867.py',s)
for n in ['prepare_gamma_one_principal_divisor_production_ownership_8821.py','prepare_gamma_one_principal_divisor_global_ownership_8821b.py']:
 script(tr(n),tr((p/n).read_text(encoding='utf-8')))
s=tr((p/'compare_gamma_one_principal_divisor_ownership_8821.py').read_text(encoding='utf-8'))
s=s.replace('==45','==46').replace("result['scratchSum']==376","result['scratchSum']=="+str(total)).replace('All 45 mathematical','All 46 mathematical')
script('compare_gamma_one_picard_hecke_comparison_ownership_8867.py',s)
s=tr((p/'record_source_gamma_one_principal_divisor_8821b.py').read_text(encoding='utf-8'))
s=re.sub(r'\b376\b',str(total),s);s=re.sub(r'== 45\b','== 46',s)
s=s.replace('"incrementModules": 45','"incrementModules": 46').replace('"linterScopes": 45','"linterScopes": 46').replace('488 required','189 required').replace('int(a[2]) == 25985','int(a[2]) == 26085').replace('Dubon Principal Divisor Reuse Assessment 2026-10-27.md',report)
s=s.replace('GAMMA ONE PRINCIPAL DIVISOR','GAMMA ONE PICARD HECKE COMPARISON').replace('actual original Gamma1 finite-divisor converse','actual original Gamma1 Picard and Hecke comparison')
script('record_source_gamma_one_picard_hecke_comparison_8867.py',s)
script('build_gamma_one_picard_hecke_comparison_8867.ps1',tr((p/'build_gamma_one_principal_divisor_8821.ps1').read_text(encoding='utf-8')))
s=tr((p/'verify_gamma_one_principal_divisor_8821.ps1').read_text(encoding='utf-8'))
script('verify_gamma_one_picard_hecke_comparison_8867.ps1',s)
s=tr((p/'archive_gamma_one_principal_divisor_canonical_8821b.py').read_text(encoding='utf-8'))
s=s.replace('actual original Gamma1 finite-divisor principalness converse with every meromorphic-function input constructed','actual original complex Gamma1 Picard-period equivalence and prime Hecke compatibility, plus native holomorphic H1 compatibility')
script('archive_gamma_one_picard_hecke_comparison_canonical_8867.py',s)
s=tr((p/'preflight_gamma_one_principal_divisor_8821.py').read_text(encoding='utf-8'))
s=s.replace("==45 and len(ns['queries'])==242 and ns['count']==376","==46 and len(ns['queries'])==128 and ns['count']=="+str(total))
s=s.replace('modules=45,queries=242,exhaustiveScratchChecks=376,proofValueChecks=488',f'modules=46,queries=128,exhaustiveScratchChecks={total},proofValueChecks=189')
script('preflight_gamma_one_picard_hecke_comparison_8867.py',s)
output('source-gamma-one-picard-hecke-comparison-scratch-ownership-8867.json',json.dumps(owners,indent=2)+'\n')
output('gamma-one-picard-hecke-comparison-preexecution-review-8867.json',json.dumps(dict(status='Prepared only. Integration requires preceding canonical PASS and archive.',modules=46,queries=128,theorems=100,constructions=28,exhaustiveScratchChecks=total,proofValueChecks=189,scopes=8,receipts=digests,expectedConsumers=26085,expectedConstructions=2717,fullGoal=boundary,scripts=[dict(path=str(p/n),sha256=sha(p/n)) for n in scripts],productionMutation=False),indent=2)+'\n')
print(json.dumps(dict(scripts=len(scripts),modules=46,checks=total,productionMutation=False)))
