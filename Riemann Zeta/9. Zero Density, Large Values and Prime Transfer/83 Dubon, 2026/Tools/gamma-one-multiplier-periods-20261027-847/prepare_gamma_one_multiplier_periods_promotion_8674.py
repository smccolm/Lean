from pathlib import Path
import json,re,hashlib,ast
p=Path(__file__).parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
stems=['source-gamma-one-closed-chain-periods-1','source-modular-free-product-1','source-cusp-correction-1','source-integral-parabolic-character-lift-1','source-gamma-one-unitary-character-periods-1c','source-gamma-one-meromorphic-multiplier-periods-1']
names=[n+'-scratch-receipt.json' for n in stems]
certs=[json.loads((p/n).read_text(encoding='utf-8')) for n in names]
digests={n:sha(p/n) for n in names}
assert tuple(sum(len(c[k]) for c in certs) for k in ['modules','queries','theoremRegistrations','constructionRegistrations'])==(42,273,207,66)
total=sum(c['exhaustiveTheorems'] for c in certs)
assert sum(c['requiredProofValueEdges'] for c in certs)==350
dependency='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> arithmetic realization of original finite Gamma1 homogeneous-coefficient Hecke characters -> full/parabolic, transpose, diamond, Picard/H1 comparison -> actual differential and period geometry -> Abel-Jacobi principal-divisor converse.'
discharged='Actual closed integer chains in the original Gamma1 orbit quotient have periods in the actual integral period lattice, with literal segment integrals. Every finite-index modular subgroup has an integral parabolic lift of each ZMod n parabolic character vanishing on finite-order elements, for every natural n including zero. The actual projective modular group is identified with C2*C3; native scalar Shapiro and transfer arguments and actual cusp-character correction construct the lift. This eliminates the torsion factors of the actual parabolic abelianization and yields a real additive logarithm of each unitary character trivial on elliptic/parabolic elements. For an ACTUAL meromorphic function with original Gamma1 divisor orders and nonzero translated cusp limits, multiplicativity and elliptic/parabolic triviality are derived, and its specific unitary multiplier is realized by actual weight-two cusp-form real periods. The signed stabilizer ramification normalization retains every nonzero level. No closed-chain period theorem, modular presentation, integral lift, cusp correction, logarithm, torsion-free quotient, multiplier character law/triviality or cusp-form-realization premise remains in these consumers.'
boundary='Analytic reciprocity and construction of meromorphic functions from the original Abel-Jacobi period condition remain. The meromorphic-multiplier consumer assumes the actual meromorphic function, its original divisor orders, unit-modulus multiplier and nonzero translated cusp limits; it does not construct that function. Global integral period/Picard, Hecke/diamond/H1, full/parabolic and transpose comparisons remain. Arithmetic realization of original finite homogeneous-coefficient Gamma1 characters, coefficient-field transport, Frobenius/inertia, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain. Complex semisimplicity, finite characters, Witt coefficients and universal deformation rings do not supply a characteristic-zero lift. 16/20; DUB-17--20 OPEN; all twenty gates unchanged.'
route='The October 27 search is converted into checked local reuse. Existing equivariant primitives and native Finsupp quotient evaluation shorten the closed-chain proof. Native ping-pong and modular generators supply the projective presentation. Existing cosetTransition multiplication replaces external coset-coordinate infrastructure. Native transfer proves the cusp sum; actual finite edge chains correct it. Native Cayley-Hamilton replaces entrywise matrix expansion, native finite abelian decomposition supplies coordinates, and native UpperHalfPlane.fixedPt replaces an explicit square-root fixed-point argument. Existing signed parabolic classification, Mobius germs, exact original Gamma1 ramification and real-period surjectivity are consumed. The unused external auxiliary branches, compatibility shims, linter suppression and external import closures are not imported. Only project imports are qualified on promotion; all audited mathematical bodies remain identical. Root pins, proof limits and the source contract are unchanged.'
status=f'The forty-two-module original Gamma1 period and multiplier scope passes 273 public axiom queries, {total} exhaustive scratch theorem checks, sixteen linters per module and six declaration-value audits with 350 required dependency checks, with zero diagnostics. Production aggregate, focused audits and sequential foundation/paper verification of the 8,674-module scope are pending.'
routefile='gamma-one-multiplier-periods-promotion-route-847.json'
archive='Tools/gamma-one-multiplier-periods-20261027-847'
report='Dubon Period and Multiplier Reuse Assessment 2026-10-27.md'
def output(n,s):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(s)
reporttext='# Dubon period and multiplier reuse assessment - 27 October 2026\n\n'+discharged+'\n\nScratch-audited; promotion and assembled verification are pending. Full acceptance remains 16/20, with DUB-17--20 open.\n\n## Reuse and exact source connection\n\nThe [live-head refresh](<Dubon Reuse Refresh 2026-10-27.md>) and [route assessment](<Dubon Reuse Route Assessment 2026-10-27.md>) are frozen research evidence. The external reference is [anthropics/fermats-last-theorem at the inspected revision](https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2), Apache-2.0. Selected proofs were adapted to actual repository objects and checked locally; the external closure was not built.\n\n'+dependency+'\n\n'+route+'\n\n## Mathematical consumers\n\n- [Closed-chain integrals](Extension/Dubon2026/SourceGammaOneClosedChainIntegral.lean): sourceGamma1_closed_chain_integrals_mem consumes an actual finite integer chain with zero orbit boundary and returns an actual integral-lattice functional agreeing with its literal straight-segment integrals.\n- [Integral parabolic lift](Extension/Dubon2026/SourceIntegralParabolicCharacterLift.lean): SourceIntegralCharacterLift.exists_int_lift consumes the actual finite-index subgroup and finite-valued parabolic character. It constructs an integer character with identical parabolic vanishing and reduction; the source Gamma1 specialization is also checked.\n- [Unitary logarithm](Extension/Dubon2026/SourceUnitaryCharacterLogarithm.lean): exists_real_logarithm derives the real character using proved torsion elimination, with no free-basis or torsion-free-quotient premise.\n- [Actual meromorphic multiplier](Extension/Dubon2026/SourceGammaOneMeromorphicMultiplierPeriods.lean): sourceGamma1_meromorphic_multiplier_eq_exp_real_period consumes the actual original-field divisor, meromorphic function, unitary multiplier, nonzero translated cusp limits and exact ramified analytic orders. It derives the multiplier hypotheses and realizes the multiplier with genuine cusp-form real periods at every nonzero level.\n\n## Verification boundary\n\n'+status+'\n\nThe strict successor audit records the Prop-valued finite-generation instance fgQ as a theorem. The rejected construction classification and all failed Lean attempts are preserved. No mathematical source or verification rule was weakened.\n\n'+boundary+'\n'
output(report,reporttext)
output(routefile,json.dumps(dict(scope=847,scopeIds=list(range(797,847)),researchScopes=[796,802],receipts=digests,dependency=dependency,discharged=discharged,remaining=boundary,route=route,precedingCanonicalScope=8632,rootPinsChanged=False,proofLimitsChanged=False,externalImport=False,fullGoal='16/20; DUB-17--20 OPEN; all twenty gates unchanged.',productionMutation=False),indent=2)+'\n')
repl={'Tools/gamma-one-real-period-surjectivity-20261027-794':archive,'Tools/gamma-one-meromorphic-principal-divisor-20261027-752':'Tools/gamma-one-real-period-surjectivity-20261027-794','appliedSourceGammaOneRealPeriodSurjectivity':'appliedSourceGammaOneMultiplierPeriods','appliedSourceGammaOneMeromorphicPrincipalDivisor':'appliedSourceGammaOneRealPeriodSurjectivity','SourceGammaOneRealPeriodSurjectivity':'SourceGammaOneMultiplierPeriods','SourceGammaOneMeromorphicPrincipalDivisor':'SourceGammaOneRealPeriodSurjectivity','gamma_one_real_period_surjectivity':'gamma_one_multiplier_periods','source-gamma-one-real-period-surjectivity':'source-gamma-one-multiplier-periods','gamma-one-real-period-surjectivity-promotion-route-794.json':routefile,'SOURCE GAMMA ONE REAL PERIOD SURJECTIVITY':'SOURCE GAMMA ONE MULTIPLIER PERIODS','actual Gamma1 real-period realization':'actual Gamma1 closed-chain periods and meromorphic multiplier realization','Actual Gamma1 real-period realization':'Actual Gamma1 closed-chain periods and meromorphic multiplier realization','8,632':'8,674','8,599':'8,632','8632':'8674','8599':'8632'}
rx=re.compile('|'.join(map(re.escape,sorted(repl,key=len,reverse=True))))
tr=lambda s:rx.sub(lambda m:repl[m[0]],s)
s=tr((p/'integrate_source_gamma_one_real_period_surjectivity_8632.py').read_text(encoding='utf-8'))
s=re.sub(r'^digests = .+$',lambda _:'digests = '+repr(digests),s,flags=re.M)
s=s.replace('(33, 33, 181, 142, 39)','(42, 42, 273, 207, 66)').replace('count == 291','count == '+str(total)).replace('"increment": 33, "queries": 181','"increment": 42, "queries": 273')
for k,v in [('dependency',dependency),('discharged',discharged),('boundary',boundary),('route',route),('status',status)]:
 assert re.search(r'^'+k+r' = .+$',s,re.M),k
 s=re.sub(r'^'+k+r' = .+$',lambda _,k=k,v=v:k+' = '+repr(v),s,flags=re.M)
owners=['SourceGammaOneClosedChainPeriodsScratchOwnership804','SourceModularFreeProductScratchOwnership810','SourceCuspCorrectionScratchOwnership817','SourceIntegralParabolicCharacterLiftScratchOwnership830','SourceGammaOneUnitaryCharacterPeriodsScratchOwnership840','SourceGammaOneMeromorphicMultiplierPeriodsScratchOwnership846']
evidence=list(names)+[n+'-audit-config.json' for n in stems]
for c in certs:
 for k in ['log','dependencyAuditLog']:
  f=Path(c[k]);evidence += [f.with_suffix(e).name for e in ['.lean','.log','.exit']]
 for row in c['files']:
  f=Path(row['path']);evidence += [f.with_suffix(e).name for e in ['.lean','.log','.exit']]
 evidence.append(Path(c['reuseReview']).name)
 rv=json.loads(Path(c['reuseReview']).read_text(encoding='utf-8'));evidence.append(Path(rv['routeAssessment']['path']).name)
pattern='(?:'+'|'.join(str(i) for i in range(796,847))+')'
families=('gamma_one','gamma-one','source_cusp','source-cusp','source_modular','source-modular','integral_parabolic','unitary-period','cusp-correction')
for f in p.iterdir():
 if f.is_file() and any(k in f.name for k in families) and f.suffix in ['.json','.py','.ps1','.txt','.log','.exit'] and re.search(r'(?<!\d)'+pattern+r'[a-z]?(?:\.|-)',f.name):evidence.append(f.name)
for prefix in ['SourceGammaOneUnitaryCharacterPeriodsAudit1','SourceModularFreeProductAudit1']:
 for f in p.glob(prefix+'*'):
  if f.is_file() and f.suffix in ['.lean','.log','.exit']:evidence.append(f.name)
for f in p.glob('source-gamma-one-unitary-character-periods-1*'):
 if f.is_file() and f.suffix=='.json':evidence.append(f.name)
for n in owners:evidence += [n+e for e in ['.lean','.log','.exit']]
folders=[f.name for f in p.iterdir() if f.is_dir() and re.search(pattern+r'[a-z]?$',f.name) and any(k in f.name for k in ['gamma-one','modular-free','cusp-correction','integral-character','integral-parabolic','unitary-character'])]
for n in evidence+folders:assert (p/n).exists(),n
a=s.index('evidence=[p/');b=s.index("for cert in certs:\n    evidence.append",a)
s=s[:a]+'evidence=[p/'+repr(routefile)+']\nevidence += [p/n for n in '+repr(sorted(set(evidence)))+']\nfor folder in '+repr(folders)+':\n    evidence += sorted(f for f in (p/folder).rglob("*") if f.is_file())\n'+s[b:]
s=s.replace("p / 'Dubon Real Period Reuse Assessment 2026-10-27.md'","p / "+repr(report)).replace('6B480D104F88BC3D76E32F0EFF4D0664EA29A9A6F6594A2F0174B57E78663B6D',sha(p/report))
oldedge='  GAMMAONEREALPERIOD8632["Every original Gamma1 real parabolic character realized by actual weight-two cusp periods. Reciprocity, Picard/Hecke/diamond/H1, all-weight arithmetic association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
newedge='  GAMMAONEREALPERIOD8632["Every original Gamma1 real parabolic character realized by actual weight-two cusp periods (DUB-17/18)"] --> GAMMAONEMULTIPLIER8674\n  GAMMAONEMULTIPLIER8674["Actual closed-chain integral periods and original-divisor meromorphic multiplier realized by cusp periods. Analytic reciprocity, meromorphic construction, Picard/Hecke/H1, all-weight arithmetic association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
s=re.sub(r'^edge = .+$',lambda _:'edge = '+repr(oldedge),s,flags=re.M)
s=re.sub(r'^arch.write_text\(.*$',lambda _:"arch.write_text(arch.read_text(encoding='utf-8').replace(edge,"+repr(newedge)+"),encoding='utf-8')",s,flags=re.M)
s=re.sub(r'^    "promotionChanges": .+$',lambda _:'    "promotionChanges": '+repr('Only project scratch imports are qualified. All audited statements, proof bodies and comments remain identical. The original Gamma1 field, all nonzero levels, literal segment periods, all natural moduli, actual modular group and signed stabilizer normalization are retained.')+',',s,flags=re.M)
a=s.index("b = re.sub('  logInfo");b=s.index(', b)',a)+len(', b)')
logline='  logInfo m!"SOURCE GAMMA ONE MULTIPLIER PERIODS AUDIT PASS: {count} theorems including private/generated declarations. Actual original Gamma1 closed-chain periods and meromorphic multiplier realization are proved. Analytic reciprocity and original arithmetic comparison remain; 16/20 gates."\n'
s=s[:a]+'b = re.sub('+repr('  logInfo m!".*"\\n')+', '+repr(logline)+', b)'+s[b:]
scripts=[]
def script(n,s):
 if n.endswith('.py'):ast.parse(s)
 output(n,s);scripts.append(n)
script('integrate_source_gamma_one_multiplier_periods_8674.py',s)
for stem in ['prepare_gamma_one_real_period_surjectivity_production_ownership','prepare_gamma_one_real_period_surjectivity_global_ownership']:
 script(tr(stem+'_8632.py'),tr((p/(stem+'_8632.py')).read_text(encoding='utf-8')))
s=tr((p/'compare_gamma_one_real_period_surjectivity_ownership_8632.py').read_text(encoding='utf-8'))
s=s.replace('len(names)==len(certs)==10','len(names)==len(certs)==6').replace('len(allmods)==len(set(allmods))==33','len(allmods)==len(set(allmods))==42').replace("result['scratchSum']==291","result['scratchSum']=="+str(total)).replace('All 33 mathematical','All 42 mathematical')
script('compare_gamma_one_multiplier_periods_ownership_8674.py',s)
s=tr((p/'record_source_gamma_one_real_period_surjectivity_8632.py').read_text(encoding='utf-8'))
s=re.sub(r'\b291\b',str(total),s);s=re.sub(r'== 33\b','== 42',s);s=re.sub(r'== 10\b','== 6',s)
s=s.replace('"incrementModules": 33','"incrementModules": 42').replace('"linterScopes": 33','"linterScopes": 42').replace('Ten declaration-value audits verify 254 required dependencies.','Six declaration-value audits verify 350 required dependency checks.').replace('int(a[2]) == 24986','int(a[2]) == 25193')
script('record_source_gamma_one_multiplier_periods_8674.py',s)
for stem in ['build_gamma_one_real_period_surjectivity','verify_gamma_one_real_period_surjectivity']:
 script(tr(stem+'_8632.ps1'),tr((p/(stem+'_8632.ps1')).read_text(encoding='utf-8')))
s=tr((p/'archive_gamma_one_real_period_surjectivity_canonical_8632.py').read_text(encoding='utf-8')).replace('Canonical PASS of the original Gamma1 real-period surjectivity.','Canonical PASS of the original Gamma1 closed-chain periods and meromorphic multiplier realization.')
script('archive_gamma_one_multiplier_periods_canonical_8674.py',s)
output('source-gamma-one-multiplier-periods-scratch-ownership-8674.json',json.dumps(owners,indent=2)+'\n')
output('gamma-one-multiplier-periods-preexecution-review-8674.json',json.dumps(dict(status='Prepared only. Integration requires preceding canonical PASS and archive.',modules=42,queries=273,theorems=207,constructions=66,exhaustiveScratchChecks=total,proofValueChecks=350,scopes=6,receipts=digests,expectedConsumers=25193,expectedConstructions=2570,fullGoal='16/20; DUB-17--20 OPEN; all twenty gates unchanged.',scripts=[dict(path=str(p/n),sha256=sha(p/n)) for n in scripts],productionMutation=False),indent=2)+'\n')
print(json.dumps(dict(scripts=len(scripts),modules=42,checks=total,productionMutation=False)))
