from pathlib import Path
from datetime import datetime, timezone
import ast,hashlib,json,re
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
stems=['source-gamma-one-inertia-1','source-gamma-one-frobenius-1','source-gamma-one-arithmetic-1']
names=[s+'-scratch-receipt.json' for s in stems]
certs=[json.loads((p/n).read_text(encoding='utf-8')) for n in names]
assert tuple(sum(len(c[k]) for c in certs) for k in ['modules','queries','theoremRegistrations','constructionRegistrations'])==(26,49,45,4)
total=sum(c['exhaustiveTheorems'] for c in certs)
edges=sum(c['requiredProofValueEdges'] for c in certs);assert edges==99
digests={n:sha(p/n) for n in names}
dependency='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> original finite Gamma1 Hecke-character realization -> actual Picard/H1/Tate realization with Frobenius and inertia -> original equivariant specialization, torsion injection and exact norm-derived Tate relations.'
discharged='For the actual original Gamma1 coefficient field and its residue image, coordinate-degree equality and genus equality now imply inertia triviality on every Tate module with residue-invertible coefficient prime. The same constructed specialization is decomposition-equivariant and injective on invertible Picard torsion. The literal Hecke principal norm, its residue formula and torsion-free divisor cancellation give exact compatibility on finite Picard torsion, without a good-reduction model of the upper Hecke correspondence. Equivariance and injectivity then derive the original Tate identity H*F = F*F*D + p, where F is coefficient arithmetic Frobenius and the Picard diamond D has label p. The inverse label in the field norm is identified explicitly with the original Picard convention. On the actual homogeneous-valued Tate dual with combined-diamond fixedness, inverse Frobenius, the existing Hecke coefficient matrix and one cyclotomic factor give Y*Hdual = Y^2 + p^(w+1) in every weight. The final consumer derives its Tate identity from the original norm and specialization; it does not assume a Frobenius quadratic.'
boundary='Actual Gamma1 j-coordinate degree equality and actual genus preservation remain open. The Frobenius and inertia statements remain conditional on those narrower geometric inputs. Combined-diamond fixedness, genuine global finite Galois/Hecke-character realization, parabolic character realization or a faithful alternative, exceptional primes, coefficient-field realization, original all-weight characteristic-zero association, local/image/regularity, automorphy and literal higher symmetric-power continuation remain. The newly derived twisted coefficient relation does not silently discharge the earlier differently normalized conditional relation. Acceptance stays 16/20; DUB-17--20 OPEN; all twenty acceptance tests are unchanged.'
route='The fresh upstream review and native reuse search were checked before expansion. Native regular-prolongation chart specialization, Kummer torsion injectivity, correspondence principal norms, primitive constant normalization, integer-divisor cancellation, Picard quotients, Tate functor and homogeneous Hecke-diamond identities are reused. The norm route avoids an unnecessary good-reduction model of the upper correspondence. Explicit additive maps and narrow torsion functor consumers resolve expensive concrete elaboration without raising proof limits. A complementary-coefficient normalization was compiled, then deferred when inverse Frobenius with the existing coefficient matrix supplied a shorter route to a genuine dual Galois action. Deferred and failed source versions remain inert evidence and are not promoted or counted. No prime range, original object, root pin, source convention or acceptance condition changes. Promoted mathematical bodies and comments are identical to their audited forms after import qualification.'
status=f'The twenty-six-module scope passes 49 public axiom queries, {total} exhaustive scratch theorem checks, sixteen linters per module and three declaration-value audits with 99 required dependency checks, with zero diagnostics. Production aggregate, focused audits and sequential foundation/paper verification of the 9,123-module scope are pending.'
report='Dubon Original Gamma One Tate Frobenius Assessment 2026-10-28.md'
routefile='gamma-one-tate-frobenius-promotion-route-1402.json'
def output(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output(report,'# Original Gamma One inertia and Tate Frobenius — 28 October 2026\n\n'+discharged+'\n\n'+dependency+'\n\n'+route+'\n\n'+status+'\n\n'+boundary+'\n\nThe [fresh reuse refresh](Dubon%20Reuse%20Refresh%202026-10-28.md) and [curve supplement](Dubon%20Curve%20Reuse%20Supplement%202026-10-28.md) distinguish inspected upstream sources from adopted proofs. Exact source snapshots, failed attempts, deferred alternatives, successful successors and checks are preserved in `Tools/gamma-one-tate-frobenius-20261028-1402/`. The frozen paper and owner-only synchronization BAT are unchanged.\n')
output(routefile,json.dumps(dict(recordedUTC=datetime.now(timezone.utc).isoformat(),dependency=dependency,discharged=discharged,remaining=boundary,route=route,receipts=digests,modules=26,queries=49,exhaustiveScratchChecks=total,proofValueChecks=99,productionMutation=False),indent=2)+'\n')
subs={'GammaOnePicardReduction':'GammaOneTateFrobenius','gamma_one_picard_reduction':'gamma_one_tate_frobenius','gamma-one-picard-reduction':'gamma-one-tate-frobenius','GammaOneHeckeNorm':'GammaOnePicardReduction','gamma_one_hecke_norm':'gamma_one_picard_reduction','gamma-one-hecke-norm':'gamma-one-picard-reduction','9097':'9123','9074':'9097','9,097':'9,123','9,074':'9,097','20261028-1358':'20261028-1402','20261028-1324':'20261028-1358'}
pat=re.compile('|'.join(re.escape(x) for x in sorted(subs,key=len,reverse=True)))
tr=lambda s:pat.sub(lambda m:subs[m[0]],s)
s=tr((p/'integrate_source_gamma_one_picard_reduction_9097.py').read_text(encoding='utf-8'))
s=re.sub(r'^digests = .+$',lambda _:'digests = '+repr(digests),s,flags=re.M)
s=s.replace('(23, 23, 36, 33, 3)','(26, 26, 49, 45, 4)').replace('assert count == 51',f'assert count == {total}')
s=s.replace('"increment": 23, "queries": 36','"increment": 26, "queries": 49')
for key,val in [('dependency',dependency),('discharged',discharged),('boundary',boundary),('route',route),('status',status)]:
 s=re.sub(r'^'+key+r' = .+$',lambda _,key=key,val=val:key+' = '+repr(val),s,flags=re.M)
s=s.replace('Original Gamma One specialization, torsion and Gauss norm','Original Gamma One inertia and Tate Frobenius')
s=s.replace('The original Gamma1 fields, coefficient Gauss rings, exact arithmetic diamond, every invertible torsion order, and the explicit coordinate-degree and genus hypotheses are retained.','The original Gamma1 fields, literal norm and diamond conventions, every residue-invertible Tate prime, every homogeneous weight, and the explicit coordinate-degree and genus hypotheses are retained.')
evidence=names+[n+'-audit-config.json' for n in stems]
owners=[Path(c['ownershipLog']).stem for c in certs]
for c in certs:
 for key in ['log','dependencyAuditLog']:
  f=Path(c[key]);evidence += [f.with_suffix(e).name for e in ['.lean','.log','.exit']]
 for row in c['files']:evidence += [Path(row['path']).name,Path(row['compileLog']).name,Path(row['compileExit']).name]
 evidence.append(Path(c['reuseReview']).name)
 rv=json.loads(Path(c['reuseReview']).read_text(encoding='utf-8'));evidence.append(Path(rv['routeAssessment']['path']).name)
pattern=r'(?<!\d)(?:'+'|'.join(str(i) for i in range(1359,1398))+r')[a-z]?(?!\d)'
for f in p.iterdir():
 if f.is_file() and f.suffix in ['.json','.py','.ps1','.txt','.log','.exit','.lean','.md'] and re.search(pattern,f.name):evidence.append(f.name)
for n in owners:evidence += [n+e for e in ['.lean','.log','.exit']]
folders=[f.name for f in p.iterdir() if f.is_dir() and re.search(pattern+r'$',f.name) and f.name.startswith('gamma-one-')]
for n in evidence+folders:assert (p/n).exists(),n
a=s.index('evidence=[p/');b=s.index('for cert in certs:\n    evidence.append',a)
s=s[:a]+'evidence=[p/'+repr(routefile)+']\nevidence += [p/n for n in '+repr(sorted(set(evidence)))+']\nfor folder in '+repr(folders)+':\n    evidence += sorted(f for f in (p/folder).rglob("*") if f.is_file())\n'+s[b:]
s=s.replace('gamma-one-tate-frobenius-promotion-route-1358.json',routefile)
s=s.replace("p / 'Dubon Original Gamma One Picard Reduction Assessment 2026-10-28.md'",'p / '+repr(report))
s=re.sub(r"assert sha\(reportSource\) == '[A-F0-9]+'",lambda _:'assert sha(reportSource) == '+repr(sha(p/report)),s)
oldedge=next(x for x in (r/'Dubon Architecture.md').read_text(encoding='utf-8').splitlines() if x.startswith('  GAMMAPICARD9097['))
newedge='  GAMMAPICARD9097["Original specialization and invertible-torsion injection from degree/genus equality; diamond Gauss preservation and exact norm residue derived (DUB-17/18)"] --> GAMMATATE9123\n  GAMMATATE9123["Original Gamma1 inertia and norm-derived Tate Frobenius from degree/genus equality; inverse-action homogeneous polynomial derived on combined-diamond fixed part. Actual degree/genus, global Galois/character realization and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
s=re.sub(r'^edge = .+$',lambda _:'edge = '+repr(oldedge),s,flags=re.M)
s=re.sub(r'^arch.write_text\(.*$',lambda _:"arch.write_text(arch.read_text(encoding='utf-8').replace(edge,"+repr(newedge)+"),encoding='utf-8')",s,flags=re.M)
a=s.index("b = re.sub('  logInfo");b=s.index(', b)',a)+len(', b)')
line='  logInfo m!"SOURCE GAMMA ONE TATE FROBENIUS AUDIT PASS: {count} theorems including private/generated declarations. Actual original inertia and norm-derived twisted Tate Frobenius from coordinate-degree/genus equality; inverse-action all-weight polynomial on the combined-diamond fixed dual. Actual geometric equalities and global arithmetic/character realization remain;16/20 gates."\n'
s=s[:a]+'b = re.sub('+repr('  logInfo m!".*"\n')+', '+repr(line)+', b)'+s[b:]
scripts=[]
def script(n,s):
 if n.endswith('.py'):ast.parse(s)
 output(n,s);scripts.append(n)
script('integrate_source_gamma_one_tate_frobenius_9123.py',s)
for n in ['prepare_gamma_one_picard_reduction_production_ownership_9097.py','prepare_gamma_one_picard_reduction_global_ownership_9097.py']:
 script(tr(n),tr((p/n).read_text(encoding='utf-8')))
s=tr((p/'compare_gamma_one_picard_reduction_ownership_9097.py').read_text(encoding='utf-8'))
s=s.replace('==23','==26').replace("result['scratchSum']==51",f"result['scratchSum']=={total}").replace('All 23 mathematical','All 26 mathematical')
script('compare_gamma_one_tate_frobenius_ownership_9123.py',s)
s=tr((p/'record_source_gamma_one_picard_reduction_9097.py').read_text(encoding='utf-8'))
s=re.sub(r'\b51\b',str(total),s);s=re.sub(r'== 23\b','== 26',s)
s=s.replace('"incrementModules": 23','"incrementModules": 26').replace('"linterScopes": 23','"linterScopes": 26')
s=s.replace('Three declaration-value audits verify 97','Three declaration-value audits verify 99').replace('int(a[2]) == 26617','int(a[2]) == 26662')
s=s.replace('Dubon Original Gamma One Picard Reduction Assessment 2026-10-28.md',report)
s=s.replace('GAMMA ONE PICARD REDUCTION','GAMMA ONE TATE FROBENIUS').replace('original Gamma One specialization, torsion and Gauss norm','original Gamma One inertia and Tate Frobenius')
script('record_source_gamma_one_tate_frobenius_9123.py',s)
for prefix in ['build','verify']:
 script(prefix+'_gamma_one_tate_frobenius_9123.ps1',tr((p/(prefix+'_gamma_one_picard_reduction_9097.ps1')).read_text(encoding='utf-8')))
s=tr((p/'archive_gamma_one_picard_reduction_canonical_9097.py').read_text(encoding='utf-8'))
s=s.replace('original Gamma One conditional specialization, invertible-torsion injectivity, diamond Gauss preservation and exact norm reduction','original Gamma One conditional inertia, norm-derived Tate Frobenius and inverse-action all-weight polynomial')
script('archive_gamma_one_tate_frobenius_canonical_9123.py',s)
s=tr((p/'preflight_gamma_one_picard_reduction_9097.py').read_text(encoding='utf-8'))
s=s.replace("==23 and len(ns['queries'])==36 and ns['count']==51",f"==26 and len(ns['queries'])==49 and ns['count']=={total}")
s=s.replace('modules=23,queries=36,exhaustiveScratchChecks=51,proofValueChecks=97',f'modules=26,queries=49,exhaustiveScratchChecks={total},proofValueChecks=99')
script('preflight_gamma_one_tate_frobenius_9123.py',s)
output('source-gamma-one-tate-frobenius-scratch-ownership-9123.json',json.dumps(owners,indent=2)+'\n')
output('gamma-one-tate-frobenius-preexecution-review-9123.json',json.dumps(dict(status='Prepared only. Integration requires predecessor canonical PASS and archive.',modules=26,queries=49,theorems=45,constructions=4,exhaustiveScratchChecks=total,proofValueChecks=99,scopes=3,receipts=digests,expectedConsumers=26662,expectedConstructions=2857,fullGoal=boundary,scripts=[dict(path=str(p/n),sha256=sha(p/n)) for n in scripts],productionMutation=False),indent=2)+'\n')
print(json.dumps(dict(scripts=len(scripts),modules=26,checks=total,proofEdges=99,productionMutation=False)))
