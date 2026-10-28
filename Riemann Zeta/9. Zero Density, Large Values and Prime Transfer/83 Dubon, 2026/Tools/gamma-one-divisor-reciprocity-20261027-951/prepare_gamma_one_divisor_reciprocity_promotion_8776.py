from pathlib import Path
import json,re,hashlib,ast
p=Path(__file__).parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
stems=['source-gamma-one-smooth-divisor-1b','source-gamma-one-smooth-divisor-period-1b','source-gamma-one-divisor-winding-1','source-modular-green-boundary-1','source-original-divisor-winding-boundary-1','source-original-winding-integral-period-1b','source-original-petersson-reciprocity-1']
names=[n+'-scratch-receipt.json' for n in stems]
certs=[json.loads((p/n).read_text(encoding='utf-8')) for n in names]
digests={n:sha(p/n) for n in names}
assert tuple(sum(len(c[k]) for c in certs) for k in ['modules','queries','theoremRegistrations','constructionRegistrations'])==(55,341,308,33)
total=sum(c['exhaustiveTheorems'] for c in certs)
assert sum(c['requiredProofValueEdges'] for c in certs)==413
dependency='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> arithmetic realization of original finite Gamma1 homogeneous-coefficient Hecke characters -> full/parabolic, transpose, diamond, Picard/H1 comparison -> actual differential and period geometry -> Abel-Jacobi principal-divisor converse -> analytic reciprocity.'
discharged='For the actual original degree-zero Gamma1 divisor, an invariant smooth comparison V is constructed with exact ramification-weighted local orders, central stabilizer multiplicities, nonzero cusp behavior and the original endpoint-period limit. The filled quotient supplies the actual logarithm and integral parabolic character. Curved Green, literal coset side pairing and the normalized smooth-domain limit identify its winding boundary sum. Integer coset potentials and the actual normalized primitive express that sum as an integer combination of actual periods; the signed-to-original bridge yields membership in the original Gamma1 integer lattice. Equal local orders split the dbar integral, using existing almost-everywhere nonvanishing. Two proved limits of the same integral yield the exact original divisor/period/Petersson reciprocity identity, including conjugation, minus sign and central normalization. No smooth comparison, winding period or limiting reciprocity identity is assumed as a certificate.'
boundary='The original meromorphic function, its exact prescribed divisor orders, nonzero cusp limits and unitary multiplier remain explicit upstream inputs. The representative divisor functional must be related to the original finite divisor class. Integral Petersson/real-period identification, multiplier triviality and the original principal-divisor converse remain. Global Picard/Hecke/diamond/H1, full/parabolic and transpose comparisons remain. Arithmetic realization of original finite homogeneous-coefficient Gamma1 characters, coefficient-field transport, Frobenius/inertia, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain. Finite characters, complex semisimplicity, Witt coefficients and universal deformation rings do not supply a characteristic-zero lift. 16/20; DUB-17--20 OPEN; all twenty gates unchanged.'
route='The October 27 search supplies pinned Apache-2.0 generic-subgroup proofs adapted to the actual original Gamma1 objects. Existing Mobius derivatives, native slash action, projective fibers, finite domain and null boundary replace bespoke geometry. Compact support gives eventual exact equality for the smooth-divisor integral. Existing normalized primitives, all-cusp limits, Green edge integrability, native rho and original S relations replace repeated analytic setup in the parabolic integer-period proof. Existing untwist nonvanishing avoids another exceptional-set construction. Direct equality of two limits gives reciprocity; the wedge identity remains proved and used upstream by the compact dipole. All substantial tasks are connected by audited declaration-VALUE dependencies to the actual source consumers. Root pins and proof limits are unchanged; promotion changes project import qualification only.'
status=f'The fifty-five-module original-divisor reciprocity scope passes 341 public axiom queries, {total} exhaustive scratch theorem checks, sixteen linters per module and seven declaration-value audits with 413 required dependency checks, with zero diagnostics. Production aggregate, focused audits and sequential foundation/paper verification of the 8,776-module scope are pending.'
archive='Tools/gamma-one-divisor-reciprocity-20261027-951'
routefile='gamma-one-divisor-reciprocity-promotion-route-951.json'
report='Dubon Original Divisor Reciprocity Reuse Assessment 2026-10-27.md'
def output(n,t):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(t)
reporttext='# Dubon original divisor reciprocity reuse assessment - 27 October 2026\n\n'+discharged+'\n\nScratch-audited; promotion and assembled verification are pending. Full acceptance remains 16/20, with DUB-17--20 open.\n\n## Reuse and exact source connection\n\nThe [live-head refresh](<Dubon Reuse Refresh 2026-10-27.md>) and [route assessment](<Dubon Reuse Route Assessment 2026-10-27.md>) retain the bounded seven-repository search evidence. Primary reference: [anthropics/fermats-last-theorem at the inspected revision](https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2), Apache-2.0. The generic-subgroup integral-period source was additionally fetched at that exact revision and read in full. Selected proofs were adapted and checked locally; the external closure was not built.\n\n'+dependency+'\n\n'+route+'\n\n## Mathematical consumers\n\n- [Actual original-divisor smooth comparison](Extension/Dubon2026/SourceGammaOneSmoothDivisorComparison.lean) derives local orders, invariance and cusp behavior.\n- [Original endpoint-period limit](Extension/Dubon2026/SourceGammaOneSmoothDivisorPeriodIntegral.lean) derives the exact original coefficient normalization.\n- [Actual filled quotient and logarithm](Extension/Dubon2026/SourceGammaOneDivisorWindingComparison.lean) construct the parabolic integer character.\n- [Actual winding boundary limit](Extension/Dubon2026/SourceGammaOneDivisorWindingBoundary.lean) derives every Green smoothness and bound input.\n- [Original integer winding period](Extension/Dubon2026/SourceGammaOneDivisorWindingIntegralPeriod.lean) consumes that character and restricts signed periods to the original lattice.\n- [Original divisor/Petersson reciprocity](Extension/Dubon2026/SourceGammaOnePeterssonReciprocity.lean) combines two proved limits of the same normalized integral. Its meromorphic-function and exact-order inputs remain explicit.\n\n## Verification boundary\n\n'+status+'\n\nFailed mathematical, import, parser and linter attempts and fresh successors are retained. No acceptance gate is closed from module or audit counts alone.\n\n'+boundary+'\n'
output(report,reporttext)
output(routefile,json.dumps(dict(scope=951,scopeIds=list(range(895,951)),receipts=digests,dependency=dependency,discharged=discharged,remaining=boundary,route=route,precedingCanonicalScope=8721,rootPinsChanged=False,proofLimitsChanged=False,externalImport=False,fullGoal='16/20; DUB-17--20 OPEN; all twenty gates unchanged.',productionMutation=False),indent=2)+'\n')
repl={'Tools/gamma-one-smooth-comparison-20261027-894':archive,'Tools/gamma-one-reciprocity-inputs-20261027-870':'Tools/gamma-one-smooth-comparison-20261027-894','appliedSourceGammaOneSmoothComparison':'appliedSourceGammaOneDivisorReciprocity','appliedSourceGammaOneReciprocityInputs':'appliedSourceGammaOneSmoothComparison','SourceGammaOneSmoothComparison':'SourceGammaOneDivisorReciprocity','SourceGammaOneReciprocityInputs':'SourceGammaOneSmoothComparison','gamma_one_smooth_comparison':'gamma_one_divisor_reciprocity','source-gamma-one-smooth-comparison':'source-gamma-one-divisor-reciprocity','gamma-one-smooth-comparison-promotion-route-894.json':routefile,'SOURCE GAMMA ONE SMOOTH COMPARISON':'SOURCE GAMMA ONE DIVISOR RECIPROCITY','actual Gamma1 smooth partition, Petersson limit and reciprocity ingredients':'actual original Gamma1 divisor and Petersson reciprocity','Actual Gamma1 smooth partition, Petersson limit and reciprocity ingredients':'Actual original Gamma1 divisor and Petersson reciprocity','8,721':'8,776','8,695':'8,721','8721':'8776','8695':'8721'}
rx=re.compile('|'.join(map(re.escape,sorted(repl,key=len,reverse=True))))
tr=lambda s:rx.sub(lambda m:repl[m[0]],s)
s=tr((p/'integrate_source_gamma_one_smooth_comparison_8721.py').read_text(encoding='utf-8'))
s=re.sub(r'^digests = .+$',lambda _:'digests = '+repr(digests),s,flags=re.M)
s=s.replace('(26, 26, 220, 186, 34)','(55, 55, 341, 308, 33)').replace('count == 273','count == '+str(total)).replace('"increment": 26, "queries": 220','"increment": 55, "queries": 341')
for k,v in [('dependency',dependency),('discharged',discharged),('boundary',boundary),('route',route),('status',status)]:
 s=re.sub(r'^'+k+r' = .+$',lambda _,k=k,v=v:k+' = '+repr(v),s,flags=re.M)
owners=['SourceGammaOneSmoothDivisorScratchOwnership909b','SourceGammaOneSmoothDivisorPeriodScratchOwnership914','SourceGammaOneDivisorWindingScratchOwnership919','SourceModularGreenBoundaryScratchOwnership925','SourceOriginalDivisorWindingBoundaryScratchOwnership935','SourceOriginalWindingIntegralPeriodScratchOwnership943b','SourceOriginalPeterssonReciprocityScratchOwnership950']
evidence=list(names)+[n+'-audit-config.json' for n in stems]
for c in certs:
 for k in ['log','dependencyAuditLog']:
  f=Path(c[k]);evidence += [f.with_suffix(e).name for e in ['.lean','.log','.exit']]
 for row in c['files']:
  f=Path(row['path']);evidence += [f.name,Path(row['compileLog']).name,Path(row['compileExit']).name]
 evidence.append(Path(c['reuseReview']).name)
 rv=json.loads(Path(c['reuseReview']).read_text(encoding='utf-8'))
 rf=Path(rv['routeAssessment']['path']);evidence.append(rf.name)
 rd=json.loads(rf.read_text(encoding='utf-8'))
 for row in rd.get('reuseChecked',[]):
  f=Path(row['path'])
  if f.is_relative_to(p):evidence.append(str(f.relative_to(p)))
pattern='(?:'+'|'.join(str(i) for i in range(895,951))+')'
for f in p.iterdir():
 if f.is_file() and f.suffix in ['.json','.py','.ps1','.txt','.log','.exit'] and re.search(r'(?<!\d)'+pattern+r'[a-z]?(?:\.|-)',f.name):evidence.append(f.name)
for n in owners:evidence += [n+e for e in ['.lean','.log','.exit']]
folders=[f.name for f in p.iterdir() if f.is_dir() and re.search(pattern+r'[a-z]?$',f.name)]
for n in evidence+folders:assert (p/n).exists(),n
a=s.index('evidence=[p/');b=s.index("for cert in certs:\n    evidence.append",a)
s=s[:a]+'evidence=[p/'+repr(routefile)+']\nevidence += [p/n for n in '+repr(sorted(set(evidence)))+']\nfor folder in '+repr(folders)+':\n    evidence += sorted(f for f in (p/folder).rglob("*") if f.is_file())\n'+s[b:]
s=s.replace("p / 'Dubon Smooth Reciprocity Reuse Assessment 2026-10-27.md'","p / "+repr(report)).replace('2F887255366AE119B38ADF61BC7923446CA69B9A077017FF8D5501408C408A23',sha(p/report))
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
oldedge=next(x for x in (r/'Dubon Architecture.md').read_text(encoding='utf-8').splitlines() if x.startswith('  GAMMAONESMOOTH8721['))
newedge='  GAMMAONESMOOTH8721["Exact original Gamma1 smooth partition and Petersson limit; wedge, parabolic logarithm and compact dipole proved (DUB-17/18)"] --> GAMMAONEDIVISOR8776\n  GAMMAONEDIVISOR8776["Actual original divisor smooth comparison, filled quotient, integer winding period and divisor/Petersson reciprocity proved. Original meromorphic input, principal-divisor converse, Picard/Hecke/H1, all-weight association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
s=re.sub(r'^edge = .+$',lambda _:'edge = '+repr(oldedge),s,flags=re.M)
s=re.sub(r'^arch.write_text\(.*$',lambda _:"arch.write_text(arch.read_text(encoding='utf-8').replace(edge,"+repr(newedge)+"),encoding='utf-8')",s,flags=re.M)
a=s.index("b = re.sub('  logInfo");b=s.index(', b)',a)+len(', b)')
logline='  logInfo m!"SOURCE GAMMA ONE DIVISOR RECIPROCITY AUDIT PASS: {count} theorems including private/generated declarations. Actual original divisor smooth comparison, filled quotient, integer winding period and divisor/Petersson reciprocity are proved. Original meromorphic input, principal-divisor converse and all-weight arithmetic remain; 16/20 gates."\n'
s=s[:a]+'b = re.sub('+repr('  logInfo m!".*"\\n')+', '+repr(logline)+', b)'+s[b:]
scripts=[]
def script(n,t):
 if n.endswith('.py'):ast.parse(t)
 output(n,t);scripts.append(n)
script('integrate_source_gamma_one_divisor_reciprocity_8776.py',s)
for stem in ['prepare_gamma_one_smooth_comparison_production_ownership','prepare_gamma_one_smooth_comparison_global_ownership']:
 script(tr(stem+'_8721.py'),tr((p/(stem+'_8721.py')).read_text(encoding='utf-8')))
s=tr((p/'compare_gamma_one_smooth_comparison_ownership_8721.py').read_text(encoding='utf-8'))
s=s.replace('len(names)==len(certs)==5','len(names)==len(certs)==7').replace('len(allmods)==len(set(allmods))==26','len(allmods)==len(set(allmods))==55').replace("result['scratchSum']==273","result['scratchSum']=="+str(total)).replace('All 26 mathematical','All 55 mathematical')
script('compare_gamma_one_divisor_reciprocity_ownership_8776.py',s)
s=tr((p/'record_source_gamma_one_smooth_comparison_8721.py').read_text(encoding='utf-8'))
s=re.sub(r'\b273\b',str(total),s);s=re.sub(r'== 26\b','== 55',s);s=re.sub(r'== 5\b','== 7',s)
s=s.replace('"incrementModules": 26','"incrementModules": 55').replace('"linterScopes": 26','"linterScopes": 55').replace('Five declaration-value audits verify 258 required dependency checks.','Seven declaration-value audits verify 413 required dependency checks.').replace('int(a[2]) == 25477','int(a[2]) == 25785')
script('record_source_gamma_one_divisor_reciprocity_8776.py',s)
for stem in ['build_gamma_one_smooth_comparison','verify_gamma_one_smooth_comparison']:
 script(tr(stem+'_8721.ps1'),tr((p/(stem+'_8721.ps1')).read_text(encoding='utf-8')))
s=tr((p/'archive_gamma_one_smooth_comparison_canonical_8721.py').read_text(encoding='utf-8')).replace('Canonical PASS of the original Gamma1 smooth partition and Petersson limit, wedge identity, parabolic logarithm and compact dipole.','Canonical PASS of actual original divisor smooth comparison, filled quotient, integer winding period and divisor/Petersson reciprocity.')
script('archive_gamma_one_divisor_reciprocity_canonical_8776.py',s)
s=tr((p/'preflight_gamma_one_smooth_comparison_8721.py').read_text(encoding='utf-8'))
s=s.replace("==26 and len(ns['queries'])==220 and ns['count']==273",f"==55 and len(ns['queries'])==341 and ns['count']=={total}")
s=s.replace('modules=26,queries=220,exhaustiveScratchChecks=273,proofValueChecks=258',f'modules=55,queries=341,exhaustiveScratchChecks={total},proofValueChecks=413')
script('preflight_gamma_one_divisor_reciprocity_8776.py',s)
output('source-gamma-one-divisor-reciprocity-scratch-ownership-8776.json',json.dumps(owners,indent=2)+'\n')
output('gamma-one-divisor-reciprocity-preexecution-review-8776.json',json.dumps(dict(status='Prepared only. Integration requires preceding canonical PASS and archive.',modules=55,queries=341,theorems=308,constructions=33,exhaustiveScratchChecks=total,proofValueChecks=413,scopes=7,receipts=digests,expectedConsumers=25785,expectedConstructions=2647,fullGoal='16/20; DUB-17--20 OPEN; all twenty gates unchanged.',scripts=[dict(path=str(p/n),sha256=sha(p/n)) for n in scripts],productionMutation=False),indent=2)+'\n')
print(json.dumps(dict(scripts=len(scripts),modules=55,checks=total,productionMutation=False)))
