from pathlib import Path
import json,re,hashlib,ast
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
stems=['source-original-finite-divisor-reciprocity-1','source-original-integral-period-duality-1b','source-original-general-multiplier-1','source-original-prescribed-residues-1b','source-meromorphic-logarithmic-primitive-1','source-gamma-one-analytic-residue-1','source-meromorphic-cusp-construction-1','source-gamma-one-principal-divisor-converse-1']
names=[n+'-scratch-receipt.json' for n in stems]
certs=[json.loads((p/n).read_text(encoding='utf-8')) for n in names]
digests={n:sha(p/n) for n in names}
assert tuple(sum(len(c[k]) for c in certs) for k in ['modules','queries','theoremRegistrations','constructionRegistrations'])==(45,242,200,42)
total=sum(c['exhaustiveTheorems'] for c in certs)
assert total==376 and sum(c['requiredProofValueEdges'] for c in certs)==488
dependency='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> arithmetic realization of original finite Gamma1 homogeneous-coefficient Hecke characters -> full/parabolic, transpose, diamond, Picard/H1 comparison -> actual differential and period geometry -> Abel-Jacobi principal-divisor converse.'
discharged='Every finite degree-zero analytic divisor on the actual original Gamma1 integral-ratio field with original integral period class is now proved literally principal. Representative correction identifies its original finite period functional; integer cocycles and the actual Petersson pairing prove the required lattice duality. Unitarization removes the unit-modulus assumption. Native Riemann-Roch constructs the actual prescribed algebraic differential, including regularity at all j-poles. Its analytic realization gives the exact ramification-weighted integer residues, slash invariance and exponential cusp decay. Point regularization, meromorphic primitive construction and multiplier gluing give an actual meromorphic function with exact orders and nonzero limits at every translated cusp. Thus no meromorphic function, multiplier, cusp limit, exact-order certificate or analytic residue coefficient remains assumed in the finite-divisor converse.'
boundary='The forward principal-divisor period implication and full original Gamma1 Picard/Hecke/diamond/H1, full/parabolic and transpose comparisons remain. Arithmetic realization of original finite homogeneous-coefficient Gamma1 characters, coefficient-field transport, Frobenius/inertia, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain. Finite characters, complex semisimplicity, Witt coefficients and universal deformation rings do not supply a characteristic-zero lift. 16/20; DUB-17--20 OPEN; all twenty gates unchanged.'
route='The October 27 pinned external search is now used through selected locally kernel-checked proofs. Native actual Gamma1 Riemann-Roch, residue surjectivity, realization germs, uniformizer logarithmic expansion, original period surjectivity and Petersson positivity discharge the geometric inputs. Native normalized wedge primitives avoid a second disk exhaustion; native q-parameter normal forms give decay from positive cusp order directly. The final converse has 240 declarations in its proof-VALUE closure, covering every public declaration of this 45-module scope except two separately axiom-checked definitional accessors optimized away by elaboration. No unrelated generalizations, external closure, root pin changes or proof-limit changes are introduced.'
status='The forty-five-module actual Gamma1 finite-divisor converse scope passes 242 public axiom queries, 376 exhaustive scratch theorem checks, sixteen linters per module and eight declaration-value audits with 488 required dependency checks, with zero diagnostics. Production aggregate, focused audits and sequential foundation/paper verification of the 8,821-module scope are pending.'
archive='Tools/gamma-one-principal-divisor-20261027-1015'
routefile='gamma-one-principal-divisor-promotion-route-1015.json'
report='Dubon Principal Divisor Reuse Assessment 2026-10-27.md'
def output(n,t):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(t)
reporttext='# Dubon principal-divisor reuse assessment - 27 October 2026\n\n'+discharged+'\n\n'+status+'\n\n## Exact source connection and reuse\n\n'+dependency+'\n\nThe [live-head refresh](<Dubon Reuse Refresh 2026-10-27.md>) and [route assessment](<Dubon Reuse Route Assessment 2026-10-27.md>) retain the bounded seven-repository search evidence. Selected Apache-2.0 proofs from [anthropics/fermats-last-theorem at the inspected revision](https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2) were adapted to the actual original Gamma1 objects. The external whole closure was not built.\n\n'+route+'\n\n## Mathematical consumers\n\n- [Original finite-divisor reciprocity](Extension/Dubon2026/SourceGammaOneFiniteDivisorReciprocity.lean) corrects the representative functional to the original finite divisor.\n- [Original integral real-period duality](Extension/Dubon2026/SourceGammaOnePeterssonIntegralRealPeriods.lean) and [general multiplier consumer](Extension/Dubon2026/SourceGammaOneGeneralMultiplierPrincipal.lean) discharge the lattice and unitary restrictions.\n- [Actual prescribed differential](Extension/Dubon2026/SourceGammaOneAnalyticDivisorDifferential.lean) constructs the residues in the original field.\n- [Actual analytic residue coefficient](Extension/Dubon2026/SourceGammaOnePrescribedResidueCoefficient.lean) derives slash invariance, decay and the integer-residue expansion.\n- [Actual meromorphic multiplier and cusp limits](Extension/Dubon2026/SourceMeromorphicPrimitiveCusps.lean) constructs the analytic function.\n- [Original finite-divisor converse](Extension/Dubon2026/SourceGammaOnePrincipalDivisorConverse.lean) assembles these proofs. Its only mathematical input beyond the actual level, finite divisor and degree zero is membership in the original integer period lattice.\n\n## Remaining boundary\n\n'+boundary+'\n\nFailed source attempts and fresh successors are preserved with their audit evidence. Module counts are verification coverage, not acceptance-gate closure.\n'
output(report,reporttext)
output(routefile,json.dumps(dict(scope=1015,scopeIds=list(range(952,1015)),receipts=digests,dependency=dependency,discharged=discharged,remaining=boundary,route=route,precedingCanonicalScope=8776,rootPinsChanged=False,proofLimitsChanged=False,externalImport=False,fullGoal='16/20; DUB-17--20 OPEN; all twenty gates unchanged.',productionMutation=False),indent=2)+'\n')
repl={'Tools/gamma-one-divisor-reciprocity-20261027-951':archive,'Tools/gamma-one-smooth-comparison-20261027-894':'Tools/gamma-one-divisor-reciprocity-20261027-951','appliedSourceGammaOneDivisorReciprocity':'appliedSourceGammaOnePrincipalDivisor','appliedSourceGammaOneSmoothComparison':'appliedSourceGammaOneDivisorReciprocity','SourceGammaOneDivisorReciprocity':'SourceGammaOnePrincipalDivisor','gamma_one_divisor_reciprocity':'gamma_one_principal_divisor','source-gamma-one-divisor-reciprocity':'source-gamma-one-principal-divisor','gamma-one-divisor-reciprocity-promotion-route-951.json':routefile,'SOURCE GAMMA ONE DIVISOR RECIPROCITY':'SOURCE GAMMA ONE PRINCIPAL DIVISOR','actual original Gamma1 divisor and Petersson reciprocity':'actual original Gamma1 finite-divisor converse','Actual original Gamma1 divisor and Petersson reciprocity':'Actual original Gamma1 finite-divisor converse','8,776':'8,821','8,721':'8,776','8776':'8821','8721':'8776'}
rx=re.compile('|'.join(map(re.escape,sorted(repl,key=len,reverse=True))))
tr=lambda s:rx.sub(lambda m:repl[m[0]],s)
s=tr((p/'integrate_source_gamma_one_divisor_reciprocity_8776.py').read_text(encoding='utf-8'))
s=re.sub(r'^digests = .+$',lambda _:'digests = '+repr(digests),s,flags=re.M)
s=s.replace('(55, 55, 341, 308, 33)','(45, 45, 242, 200, 42)').replace('count == 533','count == 376').replace('"increment": 55, "queries": 341','"increment": 45, "queries": 242')
s=s.replace('newmods = [mapping[m] for m in mods]', 'mapping["SourceGammaOneFiniteDivisorReciprocityAssembled"] = "Dubon2026.SourceGammaOneFiniteDivisorReciprocity"\nnewmods = [mapping[m] for m in mods]')
for k,v in [('dependency',dependency),('discharged',discharged),('boundary',boundary),('route',route),('status',status)]:
 s=re.sub(r'^'+k+r' = .+$',lambda _,k=k,v=v:k+' = '+repr(v),s,flags=re.M)
owners=[Path(c['ownershipLog']).stem for c in certs]
evidence=list(names)+[n+'-audit-config.json' for n in stems]
for c in certs:
 for k in ['log','dependencyAuditLog']:
  f=Path(c[k]);evidence += [f.with_suffix(e).name for e in ['.lean','.log','.exit']]
 for row in c['files']:
  f=Path(row['path']);evidence += [f.name,Path(row['compileLog']).name,Path(row['compileExit']).name]
 evidence.append(Path(c['reuseReview']).name)
 rv=json.loads(Path(c['reuseReview']).read_text(encoding='utf-8'));rf=Path(rv['routeAssessment']['path']);evidence.append(rf.name)
 rd=json.loads(rf.read_text(encoding='utf-8'))
 for row in rd.get('reuseChecked',[]):
  f=Path(row['path'])
  if f.is_relative_to(p):evidence.append(str(f.relative_to(p)))
pattern='(?:'+'|'.join(str(i) for i in range(952,1015))+')'
for f in p.iterdir():
 if f.is_file() and f.suffix in ['.json','.py','.ps1','.txt','.log','.exit'] and re.search(r'(?<!\d)'+pattern+r'[a-z]?(?:\.|-)',f.name):evidence.append(f.name)
for n in owners:evidence += [n+e for e in ['.lean','.log','.exit']]
evidence+=['SourceGammaOneFiniteDivisorReciprocityAssembled.lean']
folders=[f.name for f in p.iterdir() if f.is_dir() and re.search(pattern+r'[a-z]?$',f.name)]
for n in evidence+folders:assert(p/n).exists(),n
a=s.index('evidence=[p/');b=s.index("for cert in certs:\n    evidence.append",a)
s=s[:a]+'evidence=[p/'+repr(routefile)+']\nevidence += [p/n for n in '+repr(sorted(set(evidence)))+']\nfor folder in '+repr(folders)+':\n    evidence += sorted(f for f in (p/folder).rglob("*") if f.is_file())\n'+s[b:]
s=s.replace("p / 'Dubon Original Divisor Reciprocity Reuse Assessment 2026-10-27.md'","p / "+repr(report)).replace('33224CC25F48519DD77D53DB1E3EE6A9A0EBE172B6377E7A7EC3A632A3910D32',sha(p/report))
oldedge=next(x for x in (r/'Dubon Architecture.md').read_text(encoding='utf-8').splitlines() if x.startswith('  GAMMAONEDIVISOR8776['))
newedge='  GAMMAONEDIVISOR8776["Actual original divisor/Petersson reciprocity proved (DUB-17/18)"] --> GAMMAONEPRINCIPAL8821\n  GAMMAONEPRINCIPAL8821["Original integral period class implies literal principalness for every finite degree-zero Gamma1 analytic divisor. Actual residue differential, meromorphic function, multiplier and cusp inputs constructed. Forward implication, full Picard/Hecke/H1, all-weight association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
s=re.sub(r'^edge = .+$',lambda _:'edge = '+repr(oldedge),s,flags=re.M)
s=re.sub(r'^arch.write_text\(.*$',lambda _:"arch.write_text(arch.read_text(encoding='utf-8').replace(edge,"+repr(newedge)+"),encoding='utf-8')",s,flags=re.M)
a=s.index("b = re.sub('  logInfo");b=s.index(', b)',a)+len(', b)')
logline='  logInfo m!"SOURCE GAMMA ONE PRINCIPAL DIVISOR AUDIT PASS: {count} theorems including private/generated declarations. The original integral-period condition implies literal principalness for every finite degree-zero Gamma1 analytic divisor. The meromorphic function and its analytic inputs are constructed. Forward implication, full Picard/H1 and all-weight arithmetic remain; 16/20 gates."\n'
s=s[:a]+'b = re.sub('+repr('  logInfo m!".*"\\n')+', '+repr(logline)+', b)'+s[b:]
scripts=[]
def script(n,t):
 if n.endswith('.py'):ast.parse(t)
 output(n,t);scripts.append(n)
script('integrate_source_gamma_one_principal_divisor_8821.py',s)
for stem in ['prepare_gamma_one_divisor_reciprocity_production_ownership','prepare_gamma_one_divisor_reciprocity_global_ownership']:
 script(tr(stem+'_8776.py'),tr((p/(stem+'_8776.py')).read_text(encoding='utf-8')))
s=tr((p/'compare_gamma_one_divisor_reciprocity_ownership_8776.py').read_text(encoding='utf-8'))
s=s.replace('len(names)==len(certs)==7','len(names)==len(certs)==8').replace('len(allmods)==len(set(allmods))==55','len(allmods)==len(set(allmods))==45').replace("result['scratchSum']==533","result['scratchSum']==376").replace('All 55 mathematical','All 45 mathematical')
script('compare_gamma_one_principal_divisor_ownership_8821.py',s)
s=tr((p/'record_source_gamma_one_divisor_reciprocity_8776.py').read_text(encoding='utf-8'))
s=re.sub(r'\b533\b','376',s);s=re.sub(r'== 55\b','== 45',s);s=re.sub(r'== 7\b','== 8',s)
s=s.replace('"incrementModules": 55','"incrementModules": 45').replace('"linterScopes": 55','"linterScopes": 45').replace('Seven declaration-value audits verify 413 required dependency checks.','Eight declaration-value audits verify 488 required dependency checks.').replace('int(a[2]) == 25785','int(a[2]) == 25985')
# Keep the supplemental human-facing report synchronized with both verification stages.
s=s.replace('paths |= {r.parent / "README.md", repo / "README.md"}','paths |= {r.parent / "README.md", repo / "README.md", r / '+repr(report)+'}')
script('record_source_gamma_one_principal_divisor_8821.py',s)
for stem in ['build_gamma_one_divisor_reciprocity','verify_gamma_one_divisor_reciprocity']:
 script(tr(stem+'_8776.ps1'),tr((p/(stem+'_8776.ps1')).read_text(encoding='utf-8')))
s=tr((p/'archive_gamma_one_divisor_reciprocity_canonical_8776.py').read_text(encoding='utf-8')).replace('Canonical PASS of actual original divisor smooth comparison, filled quotient, integer winding period and divisor/Petersson reciprocity.','Canonical PASS of the actual original Gamma1 finite-divisor principalness converse with every meromorphic-function input constructed.')
script('archive_gamma_one_principal_divisor_canonical_8821.py',s)
s=tr((p/'preflight_gamma_one_divisor_reciprocity_8776.py').read_text(encoding='utf-8')).replace("==55 and len(ns['queries'])==341 and ns['count']==533","==45 and len(ns['queries'])==242 and ns['count']==376").replace('modules=55,queries=341,exhaustiveScratchChecks=533,proofValueChecks=413','modules=45,queries=242,exhaustiveScratchChecks=376,proofValueChecks=488').replace('gamma-one-reciprocity-inputs-preflight-8821','gamma-one-principal-divisor-preflight-8821')
script('preflight_gamma_one_principal_divisor_8821.py',s)
output('source-gamma-one-principal-divisor-scratch-ownership-8821.json',json.dumps(owners,indent=2)+'\n')
output('gamma-one-principal-divisor-preexecution-review-8821.json',json.dumps(dict(status='Prepared only. Integration requires preceding canonical PASS and archive.',modules=45,queries=242,theorems=200,constructions=42,exhaustiveScratchChecks=total,proofValueChecks=488,scopes=8,receipts=digests,expectedConsumers=25985,expectedConstructions=2689,fullGoal='16/20; DUB-17--20 OPEN; all twenty gates unchanged.',scripts=[dict(path=str(p/n),sha256=sha(p/n)) for n in scripts],productionMutation=False),indent=2)+'\n')
print(json.dumps(dict(scripts=len(scripts),modules=45,checks=total,productionMutation=False)))
