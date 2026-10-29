from pathlib import Path
from datetime import datetime, timezone
import ast, hashlib, json, re
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
stems=['source-gamma-one-hecke-degree-1','source-gamma-one-norm-1',
 'source-gamma-one-diamond-norm-2','source-gamma-one-diamond-reduction-1']
names=[s+'-scratch-receipt.json' for s in stems]
certs=[json.loads((p/n).read_text(encoding='utf-8')) for n in names]
assert tuple(sum(len(c[k]) for c in certs) for k in ['modules','queries','theoremRegistrations','constructionRegistrations'])==(28,85,71,14)
total=sum(c['exhaustiveTheorems'] for c in certs)
edges=sum(c['requiredProofValueEdges'] for c in certs);assert edges==184
digests={n:sha(p/n) for n in names}
dependency='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> original Gamma1 arithmetic Hecke realization -> original Picard/Tate Frobenius and inertia -> actual Hecke norm reduction with the exact arithmetic diamond.'
discharged='For every nonzero level M and prime p coprime to M, the actual Gamma1 alpha extension has degree p+1. Native coprime subgroup reduction and analytic modular quotients prove adjacent-j nonmembership; the original correspondence field is exactly the lower field with j(q^p) adjoined. Its exact modular polynomial constructs a genuine reverse automorphism and the complete p+1 embedding census, giving the literal expanded norm. The exact integral matrix D_p gamma D_p/p identifies the reverse action on all original rational functions and descends to the actual arithmetic diamond. Its lower-right label d satisfies p*d=1 modulo M; no involution or Gamma0 diamond convention is assumed. On the original arithmetic field, w*alpha=beta and w*beta=alpha*diamond. The actual beta norm therefore has the precise twisted diamond product. With integral Laurent representatives of the input and its actual diamond image, that genuine norm is integral and its residue is coefficient Frobenius of the diamond image times q-to-q^p of the input. The norm product, reverse identity, embedding census and diamond label are derived, not supplied.'
boundary='An integral representative of the actual diamond image remains an explicit narrower input in the integral reduction theorem. Producing it from input integrality alone is required for unconditional integral norm reduction. Residue degree equality, genus preservation, compatible original-to-residue place/Picard specialization and prime-to-residue torsion injectivity remain; thus original geometric Tate Frobenius and inertia remain open. Parabolic character realization or a faithful alternative, exceptional primes, coefficient-field realization, original all-weight characteristic-zero association, local/image/regularity, automorphy and literal higher symmetric-power continuation remain. 16/20; DUB-17--20 OPEN; all twenty acceptance tests unchanged.'
route='Before expanding the dependency, reuse checks selected native coprime reduction, signed index and coordinate-degree identities, modular-ratio germs, cusp bounds, level-one polynomial classification and the rational prime-step theorem. The exact modular polynomial, original finite j-extension, tensor coefficient realization and existing Laurent conjugates avoid a new generator or automorphism framework. Existing analytic realization and arithmetic diamond descent identify the entire reverse action without extension to transcendental coefficient fields. The existing Laurent unexpansion and primitive-root reduction require only the two-input diamond adaptation. A kernel timeout was resolved using separate analytic/faithfulness lemmas and proved inclusion identities, without raising proof limits. The first diamond audit correctly rejected two Prop-valued instances misregistered as constructions; the successor registers their actual theorem kind and retains every check. Root pins, original objects and full acceptance criteria are unchanged. All promoted mathematical bodies and comments are identical to their audited forms after import qualification.'
status=f'The twenty-eight-module scope passes 85 public axiom queries, {total} exhaustive scratch theorem checks, sixteen linters per module and four declaration-value audits with 184 required dependency checks, with zero diagnostics. Production aggregate, focused audits and sequential foundation/paper verification of the 9,074-module scope are pending.'
report='Dubon Original Gamma One Hecke Norm Assessment 2026-10-28.md'
routefile='gamma-one-hecke-norm-promotion-route-1324.json'
def output(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output(report,'# Original Gamma One Hecke degree, diamond and norm — 28 October 2026\n\n'+discharged+'\n\n'+dependency+'\n\n'+route+'\n\n'+status+'\n\n'+boundary+'\n\nThe [fresh reuse refresh](Dubon%20Reuse%20Refresh%202026-10-28.md) and [curve supplement](Dubon%20Curve%20Reuse%20Supplement%202026-10-28.md) distinguish inspected upstream sources from adopted proofs. Exact source snapshots, failed attempts, successful successors and checks are preserved in `Tools/gamma-one-hecke-norm-20261028-1324/`. The frozen paper and owner-only synchronization BAT are unchanged.\n')
output(routefile,json.dumps(dict(recordedUTC=datetime.now(timezone.utc).isoformat(),dependency=dependency,discharged=discharged,remaining=boundary,route=route,receipts=digests,modules=28,queries=85,exhaustiveScratchChecks=total,proofValueChecks=184,productionMutation=False),indent=2)+'\n')
subs={'GammaOneReduction':'GammaOneHeckeNorm','gamma_one_reduction':'gamma_one_hecke_norm','gamma-one-reduction':'gamma-one-hecke-norm',
 'FrobeniusDiamond':'GammaOneReduction','frobenius_diamond':'gamma_one_reduction','frobenius-diamond':'gamma-one-reduction',
 '9046':'9074','9026':'9046','9,046':'9,074','9,026':'9,046',
 '20261028-1292':'20261028-1324','20261028-1267':'20261028-1292'}
pat=re.compile('|'.join(re.escape(x) for x in sorted(subs,key=len,reverse=True)))
tr=lambda s:pat.sub(lambda m:subs[m[0]],s)
s=tr((p/'integrate_source_gamma_one_reduction_9046.py').read_text(encoding='utf-8'))
s=re.sub(r'^digests = .+$',lambda _:'digests = '+repr(digests),s,flags=re.M)
s=s.replace('(20, 20, 91, 71, 20)','(28, 28, 85, 71, 14)').replace('assert count == 218',f'assert count == {total}')
s=s.replace('"increment": 20, "queries": 91','"increment": 28, "queries": 85')
for key,val in [('dependency',dependency),('discharged',discharged),('boundary',boundary),('route',route),('status',status)]:
 s=re.sub(r'^'+key+r' = .+$',lambda _,key=key,val=val:key+' = '+repr(val),s,flags=re.M)
s=s.replace('Original Gamma One reduction and residue correspondence','Original Gamma One Hecke degree, diamond and norm')
s=s.replace('Original Gamma1 field, all nonzero levels, signed stabilizer normalization, original integer lattice and exact divisor orders are retained.', 'The original Gamma1 fields, all nonzero levels and coprime primes, the exact lower-right diamond label and the explicit integral diamond input are retained.')
evidence=names+[n+'-audit-config.json' for n in stems]
owners=[Path(c['ownershipLog']).stem for c in certs]
for c in certs:
 for key in ['log','dependencyAuditLog']:
  f=Path(c[key]);evidence += [f.with_suffix(e).name for e in ['.lean','.log','.exit']]
 for row in c['files']:evidence += [Path(row['path']).name,Path(row['compileLog']).name,Path(row['compileExit']).name]
 evidence.append(Path(c['reuseReview']).name)
 rv=json.loads(Path(c['reuseReview']).read_text(encoding='utf-8'));rf=Path(rv['routeAssessment']['path']);evidence.append(rf.name)
pattern=r'(?<!\d)(?:'+'|'.join(str(i) for i in range(1293,1326))+r')[a-z]?(?!\d)'
for f in p.iterdir():
 if f.is_file() and f.suffix in ['.json','.py','.ps1','.txt','.log','.exit','.lean','.md'] and re.search(pattern,f.name) and (f.name.startswith(('SourceGammaOne','source-gamma-one-')) or 'gamma_one_' in f.name):evidence.append(f.name)
for n in owners:evidence += [n+e for e in ['.lean','.log','.exit']]
folders=[f.name for f in p.iterdir() if f.is_dir() and re.search(pattern+r'$',f.name) and f.name.startswith('gamma-one-')]
for n in evidence+folders:assert (p/n).exists(),n
a=s.index('evidence=[p/');b=s.index('for cert in certs:\n    evidence.append',a)
s=s[:a]+'evidence=[p/'+repr(routefile)+']\nevidence += [p/n for n in '+repr(sorted(set(evidence)))+']\nfor folder in '+repr(folders)+':\n    evidence += sorted(f for f in (p/folder).rglob("*") if f.is_file())\n'+s[b:]
s=s.replace('gamma-one-hecke-norm-promotion-route-1292.json',routefile)
s=s.replace("p / 'Dubon Original Gamma One Reduction Assessment 2026-10-28.md'",'p / '+repr(report))
s=re.sub(r"assert sha\(reportSource\) == '[A-F0-9]+'",lambda _:'assert sha(reportSource) == '+repr(sha(p/report)),s)
oldedge=next(x for x in (r/'Dubon Architecture.md').read_text(encoding='utf-8').splitlines() if x.startswith('  GAMMARED9046['))
newedge='  GAMMARED9046["Original coefficient valuation, residue field, arithmetic/Hecke maps, Frobenius factorization and residue-place orders proved (DUB-17/18)"] --> GAMMANORM9074\n  GAMMANORM9074["Original Gamma1 degree p+1, adjacent-j generation, reverse automorphism, exact arithmetic diamond and norm product proved. Integral norm reduction consumes an integral diamond representative. Diamond integrality, residue degree/genus, original Picard specialization, torsion injectivity and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
s=re.sub(r'^edge = .+$',lambda _:'edge = '+repr(oldedge),s,flags=re.M)
s=re.sub(r'^arch.write_text\(.*$',lambda _:"arch.write_text(arch.read_text(encoding='utf-8').replace(edge,"+repr(newedge)+"),encoding='utf-8')",s,flags=re.M)
a=s.index("b = re.sub('  logInfo");b=s.index(', b)',a)+len(', b)')
line='  logInfo m!"SOURCE GAMMA ONE HECKE NORM AUDIT PASS: {count} theorems including private/generated declarations. Actual original degree, generation, embedding census, exact arithmetic diamond and norm product. Integral diamond input, degree/genus preservation, original Picard specialization and arithmetic realization remain;16/20 gates."\n'
s=s[:a]+'b = re.sub('+repr('  logInfo m!".*"\n')+', '+repr(line)+', b)'+s[b:]
scripts=[]
def script(n,s):
 if n.endswith('.py'):ast.parse(s)
 output(n,s);scripts.append(n)
script('integrate_source_gamma_one_hecke_norm_9074.py',s)
for n in ['prepare_gamma_one_reduction_production_ownership_9046.py','prepare_gamma_one_reduction_global_ownership_9046.py']:
 script(tr(n),tr((p/n).read_text(encoding='utf-8')))
s=tr((p/'compare_gamma_one_reduction_ownership_9046.py').read_text(encoding='utf-8'))
s=s.replace('==20','==28').replace("result['scratchSum']==218",f"result['scratchSum']=={total}").replace('All 20 mathematical','All 28 mathematical')
script('compare_gamma_one_hecke_norm_ownership_9074.py',s)
s=tr((p/'record_source_gamma_one_reduction_9046.py').read_text(encoding='utf-8'))
s=re.sub(r'\b218\b',str(total),s);s=re.sub(r'== 20\b','== 28',s)
s=s.replace('"incrementModules": 20','"incrementModules": 28').replace('"linterScopes": 20','"linterScopes": 28')
s=s.replace('Four declaration-value audits verify 96','Four declaration-value audits verify 184').replace('int(a[2]) == 26513','int(a[2]) == 26584')
s=s.replace('Dubon Original Gamma One Reduction Assessment 2026-10-28.md',report)
s=s.replace('GAMMA ONE REDUCTION','GAMMA ONE HECKE NORM').replace('original Gamma One reduction and residue correspondence','original Gamma One Hecke degree, diamond and norm')
script('record_source_gamma_one_hecke_norm_9074.py',s)
for prefix in ['build','verify']:
 script(prefix+'_gamma_one_hecke_norm_9074.ps1',tr((p/(prefix+'_gamma_one_reduction_9046.ps1')).read_text(encoding='utf-8')))
s=tr((p/'archive_gamma_one_reduction_canonical_9046.py').read_text(encoding='utf-8'))
s=s.replace('original Gamma One coefficient reduction, finite residue correspondence and Frobenius/place identities','original Gamma One degree, exact arithmetic diamond, norm product and conditional integral reduction')
script('archive_gamma_one_hecke_norm_canonical_9074.py',s)
s=tr((p/'preflight_gamma_one_reduction_9046.py').read_text(encoding='utf-8'))
s=s.replace("==20 and len(ns['queries'])==91 and ns['count']==218",f"==28 and len(ns['queries'])==85 and ns['count']=={total}")
s=s.replace('modules=20,queries=91,exhaustiveScratchChecks=218,proofValueChecks=96',f'modules=28,queries=85,exhaustiveScratchChecks={total},proofValueChecks=184')
script('preflight_gamma_one_hecke_norm_9074.py',s)
output('source-gamma-one-hecke-norm-scratch-ownership-9074.json',json.dumps(owners,indent=2)+'\n')
output('gamma-one-hecke-norm-preexecution-review-9074.json',json.dumps(dict(status='Prepared only. Integration requires predecessor canonical PASS and archive.',modules=28,queries=85,theorems=71,constructions=14,exhaustiveScratchChecks=total,proofValueChecks=184,scopes=4,receipts=digests,expectedConsumers=26584,expectedConstructions=2850,fullGoal=boundary,scripts=[dict(path=str(p/n),sha256=sha(p/n)) for n in scripts],productionMutation=False),indent=2)+'\n')
print(json.dumps(dict(scripts=len(scripts),modules=28,checks=total,proofEdges=184,productionMutation=False)))
