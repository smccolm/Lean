from pathlib import Path
import json,re,hashlib,ast
p=Path(__file__).parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
stems=['source-gamma-one-invariant-untwist-1','source-gamma-one-divisor-reciprocity-data-1','source-gamma-one-signed-reciprocity-1','source-gamma-one-log-derivative-residues-1b']
names=[n+'-scratch-receipt.json' for n in stems]
certs=[json.loads((p/n).read_text(encoding='utf-8')) for n in names]
digests={n:sha(p/n) for n in names}
assert tuple(sum(len(c[k]) for c in certs) for k in ['modules','queries','theoremRegistrations','constructionRegistrations'])==(21,108,98,10)
total=sum(c['exhaustiveTheorems'] for c in certs)
assert sum(c['requiredProofValueEdges'] for c in certs)==234
dependency='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> arithmetic realization of original finite Gamma1 homogeneous-coefficient Hecke characters -> full/parabolic, transpose, diamond, Picard/H1 comparison -> actual differential and period geometry -> Abel-Jacobi principal-divisor converse -> analytic reciprocity.'
discharged='For an actual meromorphic function with original Gamma1 divisor orders, unitary multiplier and nonzero translated cusp limits, the specific cusp-form multiplier yields an invariant untwist with exact local integer orders, nonzero cusp limits, derivative decay and an almost-everywhere logarithmic derivative formula. For an actual degree-zero analytic divisor, finite original orbit representatives and the signed stabilizer-weighted zero order sum follow from proved divisor degree and exact ramification. Actual weight-two cusp forms extend across central sign with identical endpoint periods; signed integral periods restrict into the original integer lattice, and actual multiplier and orbit data transport faithfully. Finally, the compact-support logarithmic residue integral consumes the actual original divisor and its ramification-weighted meromorphic orders and the existing actual cusp-form endpoint primitive. The simple-pole kernel normalization, finite residue decomposition and holomorphic integration by parts are proved, not assumed. All nonzero levels and original divisor/coefficient data are retained.'
boundary='The actual meromorphic function and its exact original-divisor orders remain inputs; these consumers do not construct that function from the Abel-Jacobi condition. The modular winding-period limit, Petersson comparison, analytic reciprocity and original principal-divisor converse remain. Global integral period/Picard, Hecke/diamond/H1, full/parabolic and transpose comparisons remain. Arithmetic realization of original finite homogeneous-coefficient Gamma1 characters, coefficient-field transport, Frobenius/inertia, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain. Complex semisimplicity, finite characters, Witt coefficients and universal deformation rings do not supply a characteristic-zero lift. 16/20; DUB-17--20 OPEN; all twenty gates unchanged.'
route='The October 27 reuse search is advanced through locally verified adaptations. Native meromorphic normal form and upper-half-plane analytic action replace custom untwist regularization and repeated Mobius calculations; existing endpoint primitives and cusp limits are reused. Existing original divisor degree and exact signed ramification avoid the external general residue-degree proof. Native integer-span induction returns signed periods to the original lattice. Native compact-support integration by parts, radial Haar integration, improper FTC, singular-kernel integrability and logarithmic derivative identities shorten the analytic residue proof. The actual original-divisor consumer connects those foundations to the required chain. The external closure, linter suppressions and unused generalizations are not imported. Promotion changes only project import qualification; audited mathematical bodies, root pins, proof limits and the source contract remain unchanged.'
status=f'The twenty-one-module original Gamma1 reciprocity-input scope passes 108 public axiom queries, {total} exhaustive scratch theorem checks, sixteen linters per module and four declaration-value audits with 234 required dependency checks, with zero diagnostics. Production aggregate, focused audits and sequential foundation/paper verification of the 8,695-module scope are pending.'
routefile='gamma-one-reciprocity-inputs-promotion-route-870.json'
archive='Tools/gamma-one-reciprocity-inputs-20261027-870'
report='Dubon Reciprocity Inputs Reuse Assessment 2026-10-27.md'
def output(n,t):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(t)
reporttext='# Dubon reciprocity inputs reuse assessment - 27 October 2026\n\n'+discharged+'\n\nScratch-audited; promotion and assembled verification are pending. Full acceptance remains 16/20, with DUB-17--20 open.\n\n## Reuse and exact source connection\n\nThe [live-head refresh](<Dubon Reuse Refresh 2026-10-27.md>) and [route assessment](<Dubon Reuse Route Assessment 2026-10-27.md>) are frozen research evidence. Primary reference: [anthropics/fermats-last-theorem at the inspected revision](https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2), Apache-2.0. Selected proofs are adapted to actual repository objects and checked locally; the external closure was not built.\n\n'+dependency+'\n\n'+route+'\n\n## Mathematical consumers\n\n- [Original-divisor invariant untwist](Extension/Dubon2026/SourceGammaOneInvariantUntwist.lean): sourceGamma1_meromorphic_invariant_untwist derives the cusp-form period multiplier and full untwist properties from the actual meromorphic data.\n- [Degree-zero reciprocity data](Extension/Dubon2026/SourceGammaOneDivisorReciprocityData.lean): exists_degree_zero_reciprocity_data selects actual orbit representatives and derives the weighted zero sum using the original divisor and exact signed ramification.\n- [Signed-to-original periods](Extension/Dubon2026/SourceWeightTwoSignedReciprocity.lean): integralLattice_comp_extend, multiplier_extend and orbit_iff preserve the original integer lattice, actual multiplier and upper-half-plane orbits.\n- [Actual logarithmic residue integral](Extension/Dubon2026/SourceGammaOneLogDerivativeResidues.lean): sourceGamma1_logDerivative_residue_integral consumes the original divisor, its actual meromorphic function and exact orders, a genuine weight-two cusp form and a compact C1 test function supported in the upper half-plane. The literal sum uses original divisor coefficients and ramification.\n\n## Verification boundary\n\n'+status+'\n\nAll failed attempts and fresh successors are preserved. The generic residue theorem and untwist start from genuine upstream analytic data; they do not assume the desired reciprocity or Abel-Jacobi conclusion.\n\n'+boundary+'\n'
output(report,reporttext)
output(routefile,json.dumps(dict(scope=870,scopeIds=list(range(849,870)),researchScopes=[848],receipts=digests,dependency=dependency,discharged=discharged,remaining=boundary,route=route,precedingCanonicalScope=8674,rootPinsChanged=False,proofLimitsChanged=False,externalImport=False,fullGoal='16/20; DUB-17--20 OPEN; all twenty gates unchanged.',productionMutation=False),indent=2)+'\n')
repl={'Tools/gamma-one-multiplier-periods-20261027-847':archive,'Tools/gamma-one-real-period-surjectivity-20261027-794':'Tools/gamma-one-multiplier-periods-20261027-847','appliedSourceGammaOneMultiplierPeriods':'appliedSourceGammaOneReciprocityInputs','appliedSourceGammaOneRealPeriodSurjectivity':'appliedSourceGammaOneMultiplierPeriods','SourceGammaOneMultiplierPeriods':'SourceGammaOneReciprocityInputs','SourceGammaOneRealPeriodSurjectivity':'SourceGammaOneMultiplierPeriods','gamma_one_multiplier_periods':'gamma_one_reciprocity_inputs','source-gamma-one-multiplier-periods':'source-gamma-one-reciprocity-inputs','gamma-one-multiplier-periods-promotion-route-847.json':routefile,'SOURCE GAMMA ONE MULTIPLIER PERIODS':'SOURCE GAMMA ONE RECIPROCITY INPUTS','actual Gamma1 closed-chain periods and meromorphic multiplier realization':'actual Gamma1 untwist, signed periods and original-divisor residues','Actual Gamma1 closed-chain periods and meromorphic multiplier realization':'Actual Gamma1 untwist, signed periods and original-divisor residues','8,674':'8,695','8,632':'8,674','8674':'8695','8632':'8674'}
rx=re.compile('|'.join(map(re.escape,sorted(repl,key=len,reverse=True))))
tr=lambda s:rx.sub(lambda m:repl[m[0]],s)
s=tr((p/'integrate_source_gamma_one_multiplier_periods_8674.py').read_text(encoding='utf-8'))
s=re.sub(r'^digests = .+$',lambda _:'digests = '+repr(digests),s,flags=re.M)
s=s.replace('(42, 42, 273, 207, 66)','(21, 21, 108, 98, 10)').replace('count == 352','count == '+str(total)).replace('"increment": 42, "queries": 273','"increment": 21, "queries": 108')
old='assert f.with_suffix(".exit").read_text().strip() == "0" and f.with_suffix(".log").stat().st_size == 0'
new='assert Path(item["compileExit"]).read_text().strip() == "0" and Path(item["compileLog"]).stat().st_size == 0'
assert old in s;s=s.replace(old,new)
for k,v in [('dependency',dependency),('discharged',discharged),('boundary',boundary),('route',route),('status',status)]:
 assert re.search(r'^'+k+r' = .+$',s,re.M),k
 s=re.sub(r'^'+k+r' = .+$',lambda _,k=k,v=v:k+' = '+repr(v),s,flags=re.M)
owners=['SourceGammaOneInvariantUntwistScratchOwnership858','SourceGammaOneDivisorReciprocityDataScratchOwnership860','SourceGammaOneSignedReciprocityScratchOwnership864','SourceGammaOneLogDerivativeResiduesScratchOwnership869']
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
pattern='(?:'+'|'.join(str(i) for i in range(848,870))+')'
for f in p.iterdir():
 if f.is_file() and f.suffix in ['.json','.py','.ps1','.txt','.log','.exit'] and re.search(r'(?<!\d)'+pattern+r'[a-z]?(?:\.|-)',f.name):evidence.append(f.name)
for c in certs:
 for row in c['files']:
  f=Path(row['path'])
  for ext in ['.log','.exit']:
   if f.with_suffix(ext).exists():evidence.append(f.with_suffix(ext).name)
for n in owners:evidence += [n+e for e in ['.lean','.log','.exit']]
folders=[f.name for f in p.iterdir() if f.is_dir() and re.search(pattern+r'[a-z]?$',f.name)]
for n in evidence+folders:assert (p/n).exists(),n
a=s.index('evidence=[p/');b=s.index("for cert in certs:\n    evidence.append",a)
s=s[:a]+'evidence=[p/'+repr(routefile)+']\nevidence += [p/n for n in '+repr(sorted(set(evidence)))+']\nfor folder in '+repr(folders)+':\n    evidence += sorted(f for f in (p/folder).rglob("*") if f.is_file())\n'+s[b:]
s=s.replace("p / 'Dubon Period and Multiplier Reuse Assessment 2026-10-27.md'","p / "+repr(report)).replace('8497851AF82493F3F1025005CF0C4FC125D5DFD364647DC516FFA6193F51602D',sha(p/report))
oldedge='  GAMMAONEMULTIPLIER8674["Actual closed-chain integral periods and original-divisor meromorphic multiplier realized by cusp periods. Analytic reciprocity, meromorphic construction, Picard/Hecke/H1, all-weight arithmetic association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
newedge='  GAMMAONEMULTIPLIER8674["Actual closed-chain integral periods and original-divisor meromorphic multiplier realized by cusp periods (DUB-17/18)"] --> GAMMAONERECIPROCITY8695\n  GAMMAONERECIPROCITY8695["Actual invariant untwist, signed-to-original periods, degree-zero divisor data and logarithmic residue integral. Modular reciprocity, Abel-Jacobi, Picard/Hecke/H1, all-weight association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
s=re.sub(r'^edge = .+$',lambda _:'edge = '+repr(oldedge),s,flags=re.M)
s=re.sub(r'^arch.write_text\(.*$',lambda _:"arch.write_text(arch.read_text(encoding='utf-8').replace(edge,"+repr(newedge)+"),encoding='utf-8')",s,flags=re.M)
s=re.sub(r'^    "promotionChanges": .+$',lambda _:'    "promotionChanges": '+repr('Only project scratch imports are qualified. All audited statements, proof bodies and comments remain identical. Original Gamma1 field, all nonzero levels, signed stabilizer normalization, original integer lattice and exact divisor orders are retained.')+',',s,flags=re.M)
a=s.index("b = re.sub('  logInfo");b=s.index(', b)',a)+len(', b)')
logline='  logInfo m!"SOURCE GAMMA ONE RECIPROCITY INPUTS AUDIT PASS: {count} theorems including private/generated declarations. Actual original Gamma1 invariant untwist, signed periods, divisor data and compact-support logarithmic residues are proved. Modular reciprocity and all-weight arithmetic remain; 16/20 gates."\n'
s=s[:a]+'b = re.sub('+repr('  logInfo m!".*"\\n')+', '+repr(logline)+', b)'+s[b:]
scripts=[]
def script(n,t):
 if n.endswith('.py'):ast.parse(t)
 output(n,t);scripts.append(n)
script('integrate_source_gamma_one_reciprocity_inputs_8695.py',s)
for stem in ['prepare_gamma_one_multiplier_periods_production_ownership','prepare_gamma_one_multiplier_periods_global_ownership']:
 script(tr(stem+'_8674.py'),tr((p/(stem+'_8674.py')).read_text(encoding='utf-8')))
s=tr((p/'compare_gamma_one_multiplier_periods_ownership_8674.py').read_text(encoding='utf-8'))
s=s.replace('len(names)==len(certs)==6','len(names)==len(certs)==4').replace('len(allmods)==len(set(allmods))==42','len(allmods)==len(set(allmods))==21').replace("result['scratchSum']==352","result['scratchSum']=="+str(total)).replace('All 42 mathematical','All 21 mathematical')
script('compare_gamma_one_reciprocity_inputs_ownership_8695.py',s)
s=tr((p/'record_source_gamma_one_multiplier_periods_8674.py').read_text(encoding='utf-8'))
s=re.sub(r'\b352\b',str(total),s);s=re.sub(r'== 42\b','== 21',s);s=re.sub(r'== 6\b','== 4',s)
s=s.replace('"incrementModules": 42','"incrementModules": 21').replace('"linterScopes": 42','"linterScopes": 21').replace('Six declaration-value audits verify 350 required dependency checks.','Four declaration-value audits verify 234 required dependency checks.').replace('int(a[2]) == 25193','int(a[2]) == 25291')
script('record_source_gamma_one_reciprocity_inputs_8695.py',s)
for stem in ['build_gamma_one_multiplier_periods','verify_gamma_one_multiplier_periods']:
 script(tr(stem+'_8674.ps1'),tr((p/(stem+'_8674.ps1')).read_text(encoding='utf-8')))
s=tr((p/'archive_gamma_one_multiplier_periods_canonical_8674.py').read_text(encoding='utf-8')).replace('Canonical PASS of the original Gamma1 closed-chain periods and meromorphic multiplier realization.','Canonical PASS of the original Gamma1 untwist, signed periods and compact-support logarithmic residues.')
script('archive_gamma_one_reciprocity_inputs_canonical_8695.py',s)
output('source-gamma-one-reciprocity-inputs-scratch-ownership-8695.json',json.dumps(owners,indent=2)+'\n')
output('gamma-one-reciprocity-inputs-preexecution-review-8695.json',json.dumps(dict(status='Prepared only. Integration requires preceding canonical PASS and archive.',modules=21,queries=108,theorems=98,constructions=10,exhaustiveScratchChecks=total,proofValueChecks=234,scopes=4,receipts=digests,expectedConsumers=25291,expectedConstructions=2580,fullGoal='16/20; DUB-17--20 OPEN; all twenty gates unchanged.',scripts=[dict(path=str(p/n),sha256=sha(p/n)) for n in scripts],productionMutation=False),indent=2)+'\n')
print(json.dumps(dict(scripts=len(scripts),modules=21,checks=total,productionMutation=False)))
