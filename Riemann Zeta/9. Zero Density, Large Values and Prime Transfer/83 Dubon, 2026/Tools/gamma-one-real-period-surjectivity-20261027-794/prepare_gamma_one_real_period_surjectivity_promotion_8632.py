from pathlib import Path
import json,re,hashlib,ast
p=Path(__file__).parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
stems=['source-gamma-one-'+n+('-1b' if n=='real-manin' else '-1') for n in ['real-period-injectivity','real-parabolic-periods','cusp-orbit-invariance','cusp-width-bound','exact-cusp-orbits','signed-parabolic','real-manin','real-period-upper','canonical-genus-lower','real-period-surjectivity']]
names=[n+'-scratch-receipt.json' for n in stems]
certs=[json.loads((p/n).read_text(encoding='utf-8')) for n in names]
digests={n:sha(p/n) for n in names}
assert tuple(sum(len(c[k]) for c in certs) for k in ['modules','queries','theoremRegistrations','constructionRegistrations'])==(33,181,142,39)
assert sum(c['exhaustiveTheorems'] for c in certs)==291
assert sum(c['requiredProofValueEdges'] for c in certs)==254
dependency='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> arithmetic realization of original finite Gamma1 homogeneous-coefficient Hecke characters -> full/parabolic, transpose, diamond, Picard/H1 comparison -> actual differential and period geometry -> Abel-Jacobi principal-divisor converse.'
discharged='Every real parabolic character of the ORIGINAL Gamma1 subgroup is realized by the real periods of an actual weight-two cusp form, at every nonzero level. The actual period map is a real-linear equivalence. Native fundamental-tile maximum principles prove injectivity; cusp limits prove parabolicity. Actual rational cusp and cyclic signed-coset orbits are bijective with all original j-pole places, with exact pole orders. The central-sign character extension is injective and preserves parabolicity. Reusing the generic Manin relation bound, finite-coordinate canonical degree and literal Fourier differential/cusp equivalence proves matching dimension bounds. Actual elliptic fiber surjections suffice for the required genus lower bound. No real-period, dimension, genus, cusp-count, elliptic-cardinality or character-extension hypothesis remains.'
boundary='Reciprocity and construction of meromorphic functions from the Abel-Jacobi period condition remain. Actual global integral periods and Hecke/diamond/Picard/H1, full/parabolic and transpose comparisons remain. Arithmetic realization of original finite homogeneous-coefficient Gamma1 characters, coefficient-field transport, Frobenius/inertia, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain. Complex semisimplicity, finite characters, Witt coefficients and universal deformation rings do not supply a characteristic-zero lift. 16/20; DUB-17--20 OPEN; all twenty gates unchanged.'
route='The October 27 reuse refresh and pinned primary review are applied to the direct original Gamma1 route. Existing local period primitives, finite H1, signed subgroup geometry, exact j degree, generic Manin relations, canonical degree and literal Fourier comparison are reused. The required lower bound avoids an unnecessary exact genus formula, elliptic fiber injectivity proof and independent arithmetic cusp enumeration. Only imports are qualified on promotion; audited statements and proof bodies remain identical. Failed attempts and further primary reciprocity snapshots are preserved. External import closures are not locally built. Root pins, proof limits, source fidelity and the full all-weight contract are unchanged.'
status='The thirty-three-module original Gamma1 real-period realization passes 181 public axiom queries, 291 exhaustive scratch theorem checks, sixteen linters per module and ten declaration-value audits covering 254 required dependencies, with zero diagnostics. Production aggregate, focused audits and sequential foundation/paper verification of the 8,632-module scope are pending.'
routefile='gamma-one-real-period-surjectivity-promotion-route-794.json'
archive='Tools/gamma-one-real-period-surjectivity-20261027-794'
def output(n,s):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(s)
report='Dubon Real Period Reuse Assessment 2026-10-27.md'
reporttext='# Dubon real-period reuse assessment - 27 October 2026\n\n'+discharged+'\n\nThis is a scratch-audited result; production and assembled verification are pending. The original Dubon acceptance contract remains 16/20, with DUB-17--20 open.\n\n## Reuse that shortened the proof\n\nThe [live-head refresh](Dubon Reuse Refresh 2026-10-27.md) and [route assessment](Dubon Reuse Route Assessment 2026-10-27.md) remain the frozen research record. The useful external reference is [anthropics/fermats-last-theorem at the inspected revision](https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2), Apache-2.0. Its period strategy was adapted to the repository objects; its external import closure was not built or imported.\n\n'+route+'\n\n## Exact local result\n\n[SourceGammaOneRealPeriodSurjectivity.lean](Extension/Dubon2026/SourceGammaOneRealPeriodSurjectivity.lean) exports sourceGamma1RealParabolicPeriodHom_surjective, the actual real-linear equivalence sourceGamma1RealPeriodEquiv, and sourceGamma1_exists_cuspForm_of_real_parabolic_character. The latter realizes every supplied original real parabolic character by actual cusp-form periods. The proofs consume the original period map, actual finite and cusp places, the signed-coset Manin bound, and the original field differential/cusp equivalence.\n\nThe 33 mathematical modules have 142 theorem and 39 construction registrations, 291 exhaustive theorem checks and 254 required declaration-value edges. These counts support integrity; they do not close a Dubon source gate.\n\n## Next dependency review\n\nThree additional pinned primary files were downloaded with URL, Git blob, SHA-256 and retrieval records in the archived gamma-one-period-core-reuse-795b/manifest.json. Their final interfaces and immediate imports were reviewed. The unitary-character exponential lift still uses integral parabolic-character lifting; the chain/Petersson reciprocity assembly still uses an upstream analytic reciprocity identity. The closed-chain period-lattice step uses equivariant primitives already represented locally. These candidates require further core review and local kernel checks before any reuse claim. The initial sandbox network failure is preserved under scope 795; the approved read-only retry is scope 795b.\n\n'+boundary+'\n'
output(report,reporttext)
output(routefile,json.dumps(dict(scope=794,scopeIds=list(range(756,794)),researchScopes=[795],receipts=digests,dependency=dependency,discharged=discharged,remaining=boundary,route=route,precedingCanonicalScope=8599,rootPinsChanged=False,proofLimitsChanged=False,externalImport=False,fullGoal='16/20; DUB-17--20 OPEN; all twenty gates unchanged.',productionMutation=False),indent=2)+'\n')
repl={'Tools/gamma-one-meromorphic-principal-divisor-20261027-752':archive,'Tools/gamma-one-finite-charts-divisors-20261027-740':'Tools/gamma-one-meromorphic-principal-divisor-20261027-752','appliedSourceGammaOneMeromorphicPrincipalDivisor':'appliedSourceGammaOneRealPeriodSurjectivity','appliedSourceGammaOneFiniteChartsDivisors':'appliedSourceGammaOneMeromorphicPrincipalDivisor','SourceGammaOneMeromorphicPrincipalDivisor':'SourceGammaOneRealPeriodSurjectivity','SourceGammaOneFiniteChartsDivisors':'SourceGammaOneMeromorphicPrincipalDivisor','gamma_one_meromorphic_principal_divisor':'gamma_one_real_period_surjectivity','source-gamma-one-meromorphic-principal-divisor':'source-gamma-one-real-period-surjectivity','gamma-one-meromorphic-principal-divisor-promotion-route-752.json':routefile,'SOURCE GAMMA ONE MEROMORPHIC PRINCIPAL DIVISOR':'SOURCE GAMMA ONE REAL PERIOD SURJECTIVITY','actual Gamma1 meromorphic principal-divisor conversion':'actual Gamma1 real-period realization','Actual Gamma1 meromorphic principal-divisor conversion':'Actual Gamma1 real-period realization','8,599':'8,632','8,586':'8,599','8599':'8632','8586':'8599'}
rx=re.compile('|'.join(map(re.escape,sorted(repl,key=len,reverse=True))))
tr=lambda s:rx.sub(lambda m:repl[m[0]],s)
s=tr((p/'integrate_source_gamma_one_meromorphic_principal_divisor_8599.py').read_text(encoding='utf-8'))
s=s.replace('paper-verification-8599b-console.exit','paper-verification-8599-console.exit')
s=re.sub(r'^digests = .+$',lambda _:'digests = '+repr(digests),s,flags=re.M)
s=s.replace('(13, 13, 31, 31, 0)','(33, 33, 181, 142, 39)').replace('count == 40','count == 291').replace('"increment": 13, "queries": 31','"increment": 33, "queries": 181')
for k,v in [('dependency',dependency),('discharged',discharged),('boundary',boundary),('route',route),('status',status)]:
 assert re.search(r'^'+k+r' = .+$',s,re.M),k
 s=re.sub(r'^'+k+r' = .+$',lambda _,k=k,v=v:k+' = '+repr(v),s,flags=re.M)
s=s.replace('assert not defs  # This promotion adds only theorem registrations.', 'at = at.replace(dm, "".join("\\n  ," + chr(96)*2 + n for n in defs) + dm, 1)')
owners=['SourceGammaOneRealPeriodInjectivityScratchOwnership756','SourceGammaOneRealParabolicPeriodsScratchOwnership758','SourceGammaOneCuspOrbitInvarianceScratchOwnership762','SourceGammaOneCuspWidthBoundScratchOwnership767','SourceGammaOneExactCuspOrbitsScratchOwnership774','SourceGammaOneSignedParabolicScratchOwnership777','SourceGammaOneRealManinScratchOwnership781','SourceGammaOneRealPeriodUpperScratchOwnership784','SourceGammaOneCanonicalGenusLowerScratchOwnership789','SourceGammaOneRealPeriodSurjectivityScratchOwnership793']
evidence=list(names)+[n+'-audit-config.json' for n in stems]
for c in certs:
 for k in ['log','dependencyAuditLog']:
  f=Path(c[k]);evidence += [f.with_suffix(e).name for e in ['.lean','.log','.exit']]
 for row in c['files']:
  f=Path(row['path']);evidence += [f.with_suffix(e).name for e in ['.lean','.log','.exit']]
 evidence.append(Path(c['reuseReview']).name)
 rv=json.loads(Path(c['reuseReview']).read_text(encoding='utf-8'))
 evidence.append(Path(rv['routeAssessment']['path']).name)
pattern='(?:'+'|'.join(str(i) for i in range(756,794))+'|795)'
for f in p.iterdir():
 if f.is_file() and ('gamma_one' in f.name or 'gamma-one' in f.name) and f.suffix in ['.json','.py','.ps1','.txt','.log','.exit'] and re.search(r'(?<!\d)'+pattern+r'[a-z]?(?:\.|-)',f.name):evidence.append(f.name)
for n in owners:evidence += [n+e for e in ['.lean','.log','.exit']]
folders=[f.name for f in p.iterdir() if f.is_dir() and f.name.startswith('gamma-one-') and re.search(pattern+r'[a-z]?$',f.name)]
for n in evidence+folders:assert (p/n).exists(),n
a=s.index('evidence=[p/');b=s.index("for cert in certs:\n    evidence.append",a)
s=s[:a]+'evidence=[p/'+repr(routefile)+']\nevidence += [p/n for n in '+repr(sorted(set(evidence)))+']\nfor folder in '+repr(folders)+':\n    evidence += sorted(f for f in (p/folder).rglob("*") if f.is_file())\n'+s[b:]
s=s.replace("p / 'gamma-one-period-reuse-assessment-752/Dubon Reuse Route Assessment 2026-10-27.md'","p / "+repr(report)).replace('5265FE0DF0B08207082C35A1B752D0568235A098823C87BFA9B0433230EB7D72',sha(p/report))
oldedge='  GAMMAONEPRINCIPAL8599["Original-field meromorphic principal-divisor conversion and every cusp order proved. Function construction from periods, Hecke/diamond/Picard/H1, all-weight arithmetic association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
newedge='  GAMMAONEPRINCIPAL8599["Original-field meromorphic principal-divisor conversion with every cusp order (DUB-17/18)"] --> GAMMAONEREALPERIOD8632\n  GAMMAONEREALPERIOD8632["Every original Gamma1 real parabolic character realized by actual weight-two cusp periods. Reciprocity, Picard/Hecke/diamond/H1, all-weight arithmetic association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
s=re.sub(r'^edge = .+$',lambda _:'edge = '+repr(oldedge),s,flags=re.M)
s=re.sub(r'^arch.write_text\(.*$',lambda _:"arch.write_text(arch.read_text(encoding='utf-8').replace(edge,"+repr(newedge)+"),encoding='utf-8')",s,flags=re.M)
s=re.sub(r'^    "promotionChanges": .+$',lambda _:'    "promotionChanges": '+repr('Only scratch imports are qualified. All audited statements, proof bodies and comments remain identical. The original Gamma1 field, every nonzero level, actual real period map, exact cusp places and genuine parabolic characters are retained.')+',',s,flags=re.M)
a=s.index("b = re.sub('  logInfo");b=s.index(', b)',a)+len(', b)')
logline='  logInfo m!"SOURCE GAMMA ONE REAL PERIOD SURJECTIVITY AUDIT PASS: {count} theorems including private/generated declarations. Every original real Gamma1 parabolic character is realized by an actual weight-two cusp form. Reciprocity and original arithmetic comparison remain; 16/20 gates."\n'
s=s[:a]+'b = re.sub('+repr('  logInfo m!".*"\\n')+', '+repr(logline)+', b)'+s[b:]
scripts=[]
def script(n,s):
 if n.endswith('.py'):ast.parse(s)
 output(n,s);scripts.append(n)
script('integrate_source_gamma_one_real_period_surjectivity_8632.py',s)
for stem in ['prepare_gamma_one_meromorphic_principal_divisor_production_ownership','prepare_gamma_one_meromorphic_principal_divisor_global_ownership']:
 script(tr(stem+'_8599.py'),tr((p/(stem+'_8599.py')).read_text(encoding='utf-8')))
s=tr((p/'compare_gamma_one_meromorphic_principal_divisor_ownership_8599.py').read_text(encoding='utf-8'))
s=s.replace('len(names)==len(certs)==6','len(names)==len(certs)==10').replace('len(allmods)==len(set(allmods))==13','len(allmods)==len(set(allmods))==33').replace("result['scratchSum']==40","result['scratchSum']==291").replace('All 13 mathematical','All 33 mathematical')
script('compare_gamma_one_real_period_surjectivity_ownership_8632.py',s)
s=tr((p/'record_source_gamma_one_meromorphic_principal_divisor_8599.py').read_text(encoding='utf-8'))
s=re.sub(r'\b40\b','291',s);s=re.sub(r'== 13\b','== 33',s);s=re.sub(r'== 6\b','== 10',s)
s=s.replace('"incrementModules": 13','"incrementModules": 33').replace('"linterScopes": 13','"linterScopes": 33').replace('Six declaration-value audits verify 79 required dependencies.','Ten declaration-value audits verify 254 required dependencies.').replace('int(a[2]) == 24844','int(a[2]) == 24986')
script('record_source_gamma_one_real_period_surjectivity_8632.py',s)
for stem in ['build_gamma_one_meromorphic_principal_divisor','verify_gamma_one_meromorphic_principal_divisor']:
 script(tr(stem+'_8599.ps1'),tr((p/(stem+'_8599.ps1')).read_text(encoding='utf-8')))
output('source-gamma-one-real-period-surjectivity-scratch-ownership-8632.json',json.dumps(owners,indent=2)+'\n')
output('gamma-one-real-period-surjectivity-preexecution-review-8632.json',json.dumps(dict(status='Prepared only. Integration requires preceding canonical PASS and archive.',modules=33,queries=181,theorems=142,constructions=39,exhaustiveScratchChecks=291,proofValueEdges=254,scopes=10,receipts=digests,expectedConsumers=24986,expectedConstructions=2504,fullGoal='16/20; DUB-17--20 OPEN; all twenty gates unchanged.',scripts=[dict(path=str(p/n),sha256=sha(p/n)) for n in scripts],productionMutation=False),indent=2)+'\n')
print(json.dumps(dict(scripts=len(scripts),modules=33,checks=291,productionMutation=False)))
