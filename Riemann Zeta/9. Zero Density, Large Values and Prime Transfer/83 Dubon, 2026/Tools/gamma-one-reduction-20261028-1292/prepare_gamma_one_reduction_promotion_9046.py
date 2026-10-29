from pathlib import Path
from datetime import datetime,timezone
import json,re,hashlib,ast
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
stems=['source-gamma-one-reduction-2','source-gamma-one-residue-compatibility-1',
 'source-gamma-one-residue-frobenius-1','source-gamma-one-residue-places-1']
names=[s+'-scratch-receipt.json' for s in stems]
certs=[json.loads((p/n).read_text(encoding='utf-8')) for n in names]
assert tuple(sum(len(c[k]) for c in certs) for k in ['modules','queries','theoremRegistrations','constructionRegistrations'])==(20,91,71,20)
total=sum(c['exhaustiveTheorems'] for c in certs)
edges=sum(c['requiredProofValueEdges'] for c in certs);assert edges==96
digests={n:sha(p/n) for n in names}
dependency='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> original finite Gamma1 arithmetic Hecke realization -> original Picard/Tate Frobenius and inertia -> actual function-field reduction, finite Hecke residue maps and residue-place correspondence.'
discharged='Primitive integral Laurent fractions construct the actual coefficient valuation on the original Gamma1 function field. Its literal coefficient reduction has the exact maximal-ideal kernel, actual residue image, constant restriction and nonzero scaling required for a regular prolongation. The original j-coordinate reduces to the literal j Laurent series; its residue coordinate field is finite with degree at most the original degree, and is separable under the explicitly stated perfect-residue-field hypothesis. Original arithmetic decomposition and both original Hecke maps preserve this valuation, with exact coefficient and q-substitution reduction identities. Inertia fixes the actual residue field and its genuine places; both residue Hecke maps are finite. For a decomposition element acting on residue constants by pth power, inverse coefficient action followed by absolute Frobenius is the actual constant-linear q-to-q^p map. It is integral, finite for the original finite-index subgroup containing T, and factors the original residue Hecke beta map through alpha. Its restriction on genuine residue places equals the decomposition permutation, and normalized orders are multiplied by p. These results retain the original field, valuation, Laurent embedding and maps.'
boundary='The arithmetic Frobenius action on constants remains an explicit premise. Residue degree upper bounds and finite maps do not establish degree equality or genus preservation. The original Hecke norm reduction identity, compatible original-to-residue place/Picard specialization and prime-to-residue torsion injectivity remain; thus the original geometric Tate Frobenius quadratic and inertia realization remain unproved. Parabolic character realization or a faithful alternative, exceptional primes, coefficient-field realization, original all-weight characteristic-zero association, local/image/regularity, automorphy and literal higher symmetric-power continuation remain. 16/20; DUB-17--20 OPEN; all twenty acceptance tests unchanged.'
route='Reuse checks selected native primitive-fraction scaling, reduction-frame independence, the simple pole of j, the perfect-constant separating-coordinate criterion, original decomposition and Hecke field maps, coordinate exchange, discrete-order uniqueness and Laurent Frobenius. Mathlib codRestrict and coe_inclusion avoid normalization of large concrete records without changing proof limits. The fresh pinned AINTLIB and ATLAS review records substantive candidate proofs but does not supply a verified original Gamma1 good-reduction/Picard bridge; the shorter native field route is retained. No general scheme or Jacobian framework, external import or root-pin change is introduced. All promoted mathematical bodies remain identical to their scratch-audited forms after import qualification.'
status=f'The twenty-module scope passes 91 public axiom queries, {total} exhaustive scratch theorem checks, sixteen linters per module and four declaration-value audits with 96 required dependency checks, with zero diagnostics. Production aggregate, focused audits and sequential foundation/paper verification of the 9,046-module scope are pending.'
report='Dubon Original Gamma One Reduction Assessment 2026-10-28.md'
routefile='gamma-one-reduction-promotion-route-1292.json'
def output(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output(report,'# Original Gamma One reduction and residue correspondence — 28 October 2026\n\n'+discharged+'\n\n'+dependency+'\n\n'+route+'\n\n'+status+'\n\n'+boundary+'\n\nThe [fresh reuse refresh](Dubon%20Reuse%20Refresh%202026-10-28.md) and [curve supplement](Dubon%20Curve%20Reuse%20Supplement%202026-10-28.md) distinguish reviewed sources from adopted proofs. Exact local reuse decisions and scratch evidence are retained in `Tools/gamma-one-reduction-20261028-1292/`. The frozen paper, root pins and owner-only synchronization BAT are unchanged.\n')
output(routefile,json.dumps(dict(recordedUTC=datetime.now(timezone.utc).isoformat(),dependency=dependency,discharged=discharged,remaining=boundary,route=route,receipts=digests,modules=20,queries=91,exhaustiveScratchChecks=total,proofValueChecks=96,productionMutation=False),indent=2)+'\n')
subs={'FrobeniusDiamond':'GammaOneReduction','frobenius_diamond':'gamma_one_reduction','frobenius-diamond':'gamma-one-reduction',
 'ArithmeticDiamondComparison':'FrobeniusDiamond','arithmetic_diamond_comparison':'frobenius_diamond','arithmetic-diamond-comparison':'frobenius-diamond',
 '9026':'9046','9007':'9026','9,026':'9,046','9,007':'9,026',
 '20261028-1267':'20261028-1292','20261028-1241':'20261028-1267'}
pat=re.compile('|'.join(re.escape(x) for x in sorted(subs,key=len,reverse=True)))
tr=lambda s:pat.sub(lambda m:subs[m[0]],s)
s=tr((p/'integrate_source_frobenius_diamond_9026.py').read_text(encoding='utf-8'))
s=re.sub(r'^digests = .+$',lambda _:'digests = '+repr(digests),s,flags=re.M)
s=s.replace('(19, 19, 42, 27, 15)','(20, 20, 91, 71, 20)').replace('assert count == 108',f'assert count == {total}').replace('"increment": 19, "queries": 42','"increment": 20, "queries": 91')
for key,val in [('dependency',dependency),('discharged',discharged),('boundary',boundary),('route',route),('status',status)]:
 s=re.sub(r'^'+key+r' = .+$',lambda _,key=key,val=val:key+' = '+repr(val),s,flags=re.M)
s=s.replace('Original Frobenius normalization, transfer and diamond-one character','Original Gamma One reduction and residue correspondence')
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
pattern=r'(?<!\d)(?:'+'|'.join(str(i) for i in range(1268,1293))+r')[a-z]?(?!\d)'
for f in p.iterdir():
 if f.is_file() and f.suffix in ['.json','.py','.ps1','.txt','.log','.exit','.lean','.md'] and re.search(pattern,f.name):evidence.append(f.name)
for n in owners:evidence += [n+e for e in ['.lean','.log','.exit']]
# Research bodies have their own pinned archive; preserve only mathematical failure folders here.
folders=[f.name for f in p.iterdir() if f.is_dir() and re.search(pattern+r'$',f.name) and not f.name.startswith('curve-reuse-')]
for n in evidence+folders:assert(p/n).exists(),n
a=s.index('evidence=[p/');b=s.index('for cert in certs:\n    evidence.append',a)
s=s[:a]+'evidence=[p/'+repr(routefile)+']\nevidence += [p/n for n in '+repr(sorted(set(evidence)))+']\nfor folder in '+repr(folders)+':\n    evidence += sorted(f for f in (p/folder).rglob("*") if f.is_file())\n'+s[b:]
s=s.replace('gamma-one-reduction-promotion-route-1267.json',routefile)
s=s.replace("p / 'Dubon Frobenius Normalization and Diamond Character Assessment 2026-10-28.md'","p / "+repr(report))
s=re.sub(r"assert sha\(reportSource\) == '[A-F0-9]+'",lambda _:"assert sha(reportSource) == "+repr(sha(p/report)),s)
oldedge=next(x for x in (r/'Dubon Architecture.md').read_text(encoding='utf-8').splitlines() if x.startswith('  FROBDIAM9026['))
newedge='  FROBDIAM9026["Exact conditional Frobenius normalization; ambient Galois/Hecke compatibility; native diamond transfer invariance and original full-H1 diamond-one finite character proved (DUB-17/18)"] --> GAMMARED9046\n  GAMMARED9046["Original coefficient valuation and residue field, regular prolongation, finite separating j-coordinate, arithmetic/Hecke residue maps, Frobenius factorization and exact residue-place orders proved. Degree equality, genus, norm identity, original Picard specialization, torsion injectivity and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
s=re.sub(r'^edge = .+$',lambda _:'edge = '+repr(oldedge),s,flags=re.M)
s=re.sub(r'^arch.write_text\(.*$',lambda _:"arch.write_text(arch.read_text(encoding='utf-8').replace(edge,"+repr(newedge)+"),encoding='utf-8')",s,flags=re.M)
a=s.index("b = re.sub('  logInfo");b=s.index(', b)',a)+len(', b)')
line='  logInfo m!"SOURCE GAMMA ONE REDUCTION AUDIT PASS: {count} theorems including private/generated declarations. Actual original coefficient reduction, finite residue correspondence, conditional Frobenius factorization and residue-place orders. Degree/genus preservation, original Picard specialization and arithmetic realization remain;16/20 gates."\n'
s=s[:a]+'b = re.sub('+repr('  logInfo m!".*"\\n')+', '+repr(line)+', b)'+s[b:]
scripts=[]
def script(n,s):
 if n.endswith('.py'):ast.parse(s)
 output(n,s);scripts.append(n)
script('integrate_source_gamma_one_reduction_9046.py',s)
for n in ['prepare_frobenius_diamond_production_ownership_9026.py','prepare_frobenius_diamond_global_ownership_9026.py']:
 script(tr(n),tr((p/n).read_text(encoding='utf-8')))
s=tr((p/'compare_frobenius_diamond_ownership_9026.py').read_text(encoding='utf-8'))
s=s.replace('==19','==20').replace('==3','==4').replace("result['scratchSum']==108",f"result['scratchSum']=={total}").replace('All 19 mathematical','All 20 mathematical')
script('compare_gamma_one_reduction_ownership_9046.py',s)
s=tr((p/'record_source_frobenius_diamond_9026.py').read_text(encoding='utf-8'))
s=re.sub(r'\b108\b',str(total),s);s=re.sub(r'== 19\b','== 20',s);s=re.sub(r'== 3\b','== 4',s)
s=s.replace('"incrementModules": 19','"incrementModules": 20').replace('"linterScopes": 19','"linterScopes": 20')
s=s.replace('Three declaration-value audits verify 60','Four declaration-value audits verify 96').replace('int(a[2]) == 26442','int(a[2]) == 26513')
s=s.replace('Dubon Frobenius Normalization and Diamond Character Assessment 2026-10-28.md',report)
s=s.replace('FROBENIUS DIAMOND','GAMMA ONE REDUCTION').replace('original conditional Frobenius normalization, transfer and diamond-one character','original Gamma One reduction and residue correspondence')
script('record_source_gamma_one_reduction_9046.py',s)
for prefix in ['build','verify']:
 script(prefix+'_gamma_one_reduction_9046.ps1',tr((p/(prefix+'_frobenius_diamond_9026.ps1')).read_text(encoding='utf-8')))
s=tr((p/'archive_frobenius_diamond_canonical_9026.py').read_text(encoding='utf-8'))
s=s.replace('original conditional Frobenius normalization, native diamond transfer invariance and full-H1 diamond-one character','original Gamma One coefficient reduction, finite residue correspondence and Frobenius/place identities')
script('archive_gamma_one_reduction_canonical_9046.py',s)
s=tr((p/'preflight_frobenius_diamond_9026.py').read_text(encoding='utf-8'))
s=s.replace("==19 and len(ns['queries'])==42 and ns['count']==108",f"==20 and len(ns['queries'])==91 and ns['count']=={total}")
s=s.replace('modules=19,queries=42,exhaustiveScratchChecks=108,proofValueChecks=60',f'modules=20,queries=91,exhaustiveScratchChecks={total},proofValueChecks=96')
script('preflight_gamma_one_reduction_9046.py',s)
output('source-gamma-one-reduction-scratch-ownership-9046.json',json.dumps(owners,indent=2)+'\n')
output('gamma-one-reduction-preexecution-review-9046.json',json.dumps(dict(status='Prepared only. Integration requires predecessor canonical PASS and archive.',modules=20,queries=91,theorems=71,constructions=20,exhaustiveScratchChecks=total,proofValueChecks=96,scopes=4,receipts=digests,expectedConsumers=26513,expectedConstructions=2836,fullGoal=boundary,scripts=[dict(path=str(p/n),sha256=sha(p/n)) for n in scripts],productionMutation=False),indent=2)+'\n')
print(json.dumps(dict(scripts=len(scripts),modules=20,checks=total,proofEdges=96,productionMutation=False)))
