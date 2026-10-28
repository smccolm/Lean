from pathlib import Path
import json,re,hashlib,ast
p=Path(__file__).parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
stems=['source-gamma-one-untwist-wedge-1','source-gamma-one-smooth-partition-1b','source-gamma-one-petersson-smooth-limit-1','source-modular-parabolic-winding-log-1','source-complex-dipole-1']
names=[n+'-scratch-receipt.json' for n in stems]
certs=[json.loads((p/n).read_text(encoding='utf-8')) for n in names]
digests={n:sha(p/n) for n in names}
assert tuple(sum(len(c[k]) for c in certs) for k in ['modules','queries','theoremRegistrations','constructionRegistrations'])==(26,220,186,34)
total=sum(c['exhaustiveTheorems'] for c in certs)
assert sum(c['requiredProofValueEdges'] for c in certs)==258
dependency='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> arithmetic realization of original finite Gamma1 homogeneous-coefficient Hecke characters -> full/parabolic, transpose, diamond, Picard/H1 comparison -> actual differential and period geometry -> Abel-Jacobi principal-divisor converse -> analytic reciprocity.'
discharged='The actual original-divisor untwist satisfies the compact C2 wedge/residue identity through proved local integer orders. The literal smooth modular coset partition is constructed with compact support, finite overlap and exact orbit mass. For original Gamma1 weight-two cusp forms, native fundamental-domain unfolding and two-element central fibers prove the source-normalized planar Petersson limit, including integrability and the factor one half on the literal closed coset domain. For an actual nonvanishing invariant C1 function with nonzero finite translated cusp limits, the logarithm, derivative and integral additive character are constructed, and the existing parabolic classification proves squared-trace-four vanishing. Finally an actual compact smooth dipole has orders +1 at s and -1 at b and exact integral pi times the endpoint difference. None of these analytic conclusions is supplied as a certificate.'
boundary='The original meromorphic function and its exact divisor orders remain inputs to the untwist consumer. The globally invariant smooth comparison V, exact orbit multiplicities and degree-zero cancellation, filled quotient, winding-period/Petersson assembly, analytic reciprocity and original principal-divisor converse remain. Global integral period/Picard, Hecke/diamond/H1, full/parabolic and transpose comparisons remain. Arithmetic realization of original finite homogeneous-coefficient Gamma1 characters, coefficient-field transport, Frobenius/inertia, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain. Complex semisimplicity, finite characters, Witt coefficients and universal deformation rings do not supply a characteristic-zero lift. 16/20; DUB-17--20 OPEN; all twenty gates unchanged.'
route='The October 27 reuse search is advanced by locally checked adaptations of pinned Apache-2.0 primary proofs. Existing generic projective domains, finite volume and null boundary replace bespoke finite tilings; native fiber equivalence, unfolding and dominated convergence give the exact central factor. Native proper discontinuity and the Mobius imaginary-part identity construct the source partition. Native exponential covering and uniqueness replace extra lift and local-constancy infrastructure, and the existing parabolic classification replaces an external Period wrapper. The existing wedge/residue theorem and antiholomorphic derivative supply the exact dipole pairing. Unused helpers and external linter suppressions are omitted; root pins and proof limits are unchanged. Promotion changes project import qualification only.'
status=f'The twenty-six-module smooth reciprocity ingredient scope passes 220 public axiom queries, {total} exhaustive scratch theorem checks, sixteen linters per module and five declaration-value audits with 258 required dependency checks, with zero diagnostics. Production aggregate, focused audits and sequential foundation/paper verification of the 8,721-module scope are pending.'
routefile='gamma-one-smooth-comparison-promotion-route-894.json'
archive='Tools/gamma-one-smooth-comparison-20261027-894'
report='Dubon Smooth Reciprocity Reuse Assessment 2026-10-27.md'
def output(n,t):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(t)
reporttext='# Dubon smooth reciprocity reuse assessment - 27 October 2026\n\n'+discharged+'\n\nScratch-audited; promotion and assembled verification are pending. Full acceptance remains 16/20, with DUB-17--20 open.\n\n## Reuse and exact source connection\n\nThe [live-head refresh](<Dubon Reuse Refresh 2026-10-27.md>) and [route assessment](<Dubon Reuse Route Assessment 2026-10-27.md>) retain the bounded search evidence. Primary reference: [anthropics/fermats-last-theorem at the inspected revision](https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2), Apache-2.0. Selected proofs are adapted and checked locally; the external closure was not built.\n\n'+dependency+'\n\n'+route+'\n\n## Mathematical consumers\n\n- [Actual original-divisor wedge identity](Extension/Dubon2026/SourceGammaOneUntwistWedgeIntegral.lean) consumes original divisor orders and the actual cusp primitive.\n- [Actual Gamma1 smooth partition](Extension/Dubon2026/SourceGammaOneSmoothPartition.lean) constructs the literal source cutoff family and derives all its support and orbit-sum properties.\n- [Original cusp-form Petersson limit](Extension/Dubon2026/SourceGammaOnePeterssonSmoothLimit.lean) derives signed invariance and integrability and proves the exact factor one half.\n- [Parabolic logarithm construction](Extension/Dubon2026/SourceModularParabolicWindingLog.lean) constructs the logarithm and integer character with literal trace-four vanishing. The actual filled comparison quotient remains to be constructed.\n- [Compact dipole](Extension/Dubon2026/SourceUpperHalfPlaneDipole.lean) constructs the local factors needed for V with exact orders and exact integral pairing. It does not assert V already exists.\n\n## Verification boundary\n\n'+status+'\n\nAll failed attempts and successors are preserved. No meromorphic realization, reciprocity identity, characteristic-zero lift or higher symmetric-power continuation is assumed to be proved by these consumers.\n\n'+boundary+'\n'
output(report,reporttext)
output(routefile,json.dumps(dict(scope=894,scopeIds=[871,872,873,874,875,876,877,878,879,880,881,882,883,884,885,887,888,890,891,893],researchScopes=[886,889],receipts=digests,dependency=dependency,discharged=discharged,remaining=boundary,route=route,precedingCanonicalScope=8695,rootPinsChanged=False,proofLimitsChanged=False,externalImport=False,fullGoal='16/20; DUB-17--20 OPEN; all twenty gates unchanged.',productionMutation=False),indent=2)+'\n')
repl={'Tools/gamma-one-reciprocity-inputs-20261027-870':archive,'Tools/gamma-one-multiplier-periods-20261027-847':'Tools/gamma-one-reciprocity-inputs-20261027-870','appliedSourceGammaOneReciprocityInputs':'appliedSourceGammaOneSmoothComparison','appliedSourceGammaOneMultiplierPeriods':'appliedSourceGammaOneReciprocityInputs','SourceGammaOneReciprocityInputs':'SourceGammaOneSmoothComparison','SourceGammaOneMultiplierPeriods':'SourceGammaOneReciprocityInputs','gamma_one_reciprocity_inputs':'gamma_one_smooth_comparison','source-gamma-one-reciprocity-inputs':'source-gamma-one-smooth-comparison','gamma-one-reciprocity-inputs-promotion-route-870.json':routefile,'SOURCE GAMMA ONE RECIPROCITY INPUTS':'SOURCE GAMMA ONE SMOOTH COMPARISON','actual Gamma1 untwist, signed periods and original-divisor residues':'actual Gamma1 smooth partition, Petersson limit and reciprocity ingredients','Actual Gamma1 untwist, signed periods and original-divisor residues':'Actual Gamma1 smooth partition, Petersson limit and reciprocity ingredients','8,695':'8,721','8,674':'8,695','8695':'8721','8674':'8695'}
rx=re.compile('|'.join(map(re.escape,sorted(repl,key=len,reverse=True))))
tr=lambda s:rx.sub(lambda m:repl[m[0]],s)
s=tr((p/'integrate_source_gamma_one_reciprocity_inputs_8695.py').read_text(encoding='utf-8'))
s=re.sub(r'^digests = .+$',lambda _:'digests = '+repr(digests),s,flags=re.M)
s=s.replace('(21, 21, 108, 98, 10)','(26, 26, 220, 186, 34)').replace('count == 156','count == '+str(total)).replace('"increment": 21, "queries": 108','"increment": 26, "queries": 220')
for k,v in [('dependency',dependency),('discharged',discharged),('boundary',boundary),('route',route),('status',status)]:
 assert re.search(r'^'+k+r' = .+$',s,re.M),k
 s=re.sub(r'^'+k+r' = .+$',lambda _,k=k,v=v:k+' = '+repr(v),s,flags=re.M)
owners=['SourceGammaOneUntwistWedgeScratchOwnership874','SourceGammaOneSmoothPartitionScratchOwnership878b','SourceGammaOnePeterssonSmoothLimitScratchOwnership885','SourceModularParabolicWindingLogScratchOwnership890','SourceComplexDipoleScratchOwnership893']
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
pattern='(?:'+'|'.join(str(i) for i in range(871,894) if i!=892)+')'
for f in p.iterdir():
 if f.is_file() and f.suffix in ['.json','.py','.ps1','.txt','.log','.exit'] and re.search(r'(?<!\d)'+pattern+r'[a-z]?(?:\.|-)',f.name):evidence.append(f.name)
for n in owners:evidence += [n+e for e in ['.lean','.log','.exit']]
folders=[f.name for f in p.iterdir() if f.is_dir() and re.search(pattern+r'[a-z]?$',f.name)]
for n in evidence+folders:assert (p/n).exists(),n
a=s.index('evidence=[p/');b=s.index("for cert in certs:\n    evidence.append",a)
s=s[:a]+'evidence=[p/'+repr(routefile)+']\nevidence += [p/n for n in '+repr(sorted(set(evidence)))+']\nfor folder in '+repr(folders)+':\n    evidence += sorted(f for f in (p/folder).rglob("*") if f.is_file())\n'+s[b:]
s=s.replace("p / 'Dubon Reciprocity Inputs Reuse Assessment 2026-10-27.md'","p / "+repr(report)).replace('D32B896A3B5B86CE8E8EF1885E7FE74F66BD70DD7C7463DF7039DEFDCD2B9339',sha(p/report))
oldedge='  GAMMAONERECIPROCITY8695["Actual invariant untwist, signed-to-original periods, degree-zero divisor data and logarithmic residue integral. Modular reciprocity, Abel-Jacobi, Picard/Hecke/H1, all-weight association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
newedge='  GAMMAONERECIPROCITY8695["Actual invariant untwist, signed-to-original periods, degree-zero divisor data and logarithmic residue integral (DUB-17/18)"] --> GAMMAONESMOOTH8721\n  GAMMAONESMOOTH8721["Exact original Gamma1 smooth partition and Petersson limit; wedge, parabolic logarithm and compact dipole proved. Invariant V, winding-period comparison, reciprocity, Abel-Jacobi, Picard/Hecke/H1, all-weight association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
s=re.sub(r'^edge = .+$',lambda _:'edge = '+repr(oldedge),s,flags=re.M)
s=re.sub(r'^arch.write_text\(.*$',lambda _:"arch.write_text(arch.read_text(encoding='utf-8').replace(edge,"+repr(newedge)+"),encoding='utf-8')",s,flags=re.M)
a=s.index("b = re.sub('  logInfo");b=s.index(', b)',a)+len(', b)')
logline='  logInfo m!"SOURCE GAMMA ONE SMOOTH COMPARISON AUDIT PASS: {count} theorems including private/generated declarations. Original Gamma1 smooth partition and Petersson limit, wedge identity, parabolic logarithm and compact dipole are proved. Invariant V, analytic reciprocity and all-weight arithmetic remain; 16/20 gates."\n'
s=s[:a]+'b = re.sub('+repr('  logInfo m!".*"\\n')+', '+repr(logline)+', b)'+s[b:]
scripts=[]
def script(n,t):
 if n.endswith('.py'):ast.parse(t)
 output(n,t);scripts.append(n)
script('integrate_source_gamma_one_smooth_comparison_8721.py',s)
for stem in ['prepare_gamma_one_reciprocity_inputs_production_ownership','prepare_gamma_one_reciprocity_inputs_global_ownership']:
 script(tr(stem+'_8695.py'),tr((p/(stem+'_8695.py')).read_text(encoding='utf-8')))
s=tr((p/'compare_gamma_one_reciprocity_inputs_ownership_8695.py').read_text(encoding='utf-8'))
s=s.replace('len(names)==len(certs)==4','len(names)==len(certs)==5').replace('len(allmods)==len(set(allmods))==21','len(allmods)==len(set(allmods))==26').replace("result['scratchSum']==156","result['scratchSum']=="+str(total)).replace('All 21 mathematical','All 26 mathematical')
script('compare_gamma_one_smooth_comparison_ownership_8721.py',s)
s=tr((p/'record_source_gamma_one_reciprocity_inputs_8695.py').read_text(encoding='utf-8'))
s=re.sub(r'\b156\b',str(total),s);s=re.sub(r'== 21\b','== 26',s);s=re.sub(r'== 4\b','== 5',s)
s=s.replace('"incrementModules": 21','"incrementModules": 26').replace('"linterScopes": 21','"linterScopes": 26').replace('Four declaration-value audits verify 234 required dependency checks.','Five declaration-value audits verify 258 required dependency checks.').replace('int(a[2]) == 25291','int(a[2]) == 25477')
script('record_source_gamma_one_smooth_comparison_8721.py',s)
for stem in ['build_gamma_one_reciprocity_inputs','verify_gamma_one_reciprocity_inputs']:
 script(tr(stem+'_8695.ps1'),tr((p/(stem+'_8695.ps1')).read_text(encoding='utf-8')))
s=tr((p/'archive_gamma_one_reciprocity_inputs_canonical_8695.py').read_text(encoding='utf-8')).replace('Canonical PASS of the original Gamma1 untwist, signed periods and compact-support logarithmic residues.','Canonical PASS of the original Gamma1 smooth partition and Petersson limit, wedge identity, parabolic logarithm and compact dipole.')
script('archive_gamma_one_smooth_comparison_canonical_8721.py',s)
s=tr((p/'preflight_gamma_one_reciprocity_inputs_8695.py').read_text(encoding='utf-8'))
s=s.replace("==21 and len(ns['queries'])==108 and ns['count']==156",f"==26 and len(ns['queries'])==220 and ns['count']=={total}")
s=s.replace('modules=21,queries=108,exhaustiveScratchChecks=156,proofValueChecks=234',f'modules=26,queries=220,exhaustiveScratchChecks={total},proofValueChecks=258')
script('preflight_gamma_one_smooth_comparison_8721.py',s)
output('source-gamma-one-smooth-comparison-scratch-ownership-8721.json',json.dumps(owners,indent=2)+'\n')
output('gamma-one-smooth-comparison-preexecution-review-8721.json',json.dumps(dict(status='Prepared only. Integration requires preceding canonical PASS and archive.',modules=26,queries=220,theorems=186,constructions=34,exhaustiveScratchChecks=total,proofValueChecks=258,scopes=5,receipts=digests,expectedConsumers=25477,expectedConstructions=2614,fullGoal='16/20; DUB-17--20 OPEN; all twenty gates unchanged.',scripts=[dict(path=str(p/n),sha256=sha(p/n)) for n in scripts],productionMutation=False),indent=2)+'\n')
print(json.dumps(dict(scripts=len(scripts),modules=26,checks=total,productionMutation=False)))
