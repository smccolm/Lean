from pathlib import Path
import ast,json,re,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
spec=[('620b','source-gamma-one-function-field-10b-scratch-receipt.json','gamma1-function-field-finite-route-620b.json'),('622','source-gamma-one-hecke-field-5-scratch-receipt.json','gamma1-finite-hecke-field-route-622.json'),('624b','source-gamma-one-hecke-picard-2b-scratch-receipt.json','gamma1-actual-picard-hecke-route-624b.json'),('625','source-gamma-one-arithmetic-9-scratch-receipt.json','gamma1-arithmetic-hecke-picard-route-625.json')]
certs=[json.loads((p/n).read_text()) for _,n,_ in spec]
digests={n:sha(p/n) for _,n,_ in spec}
assert all(c['exit']==c['diagnostics']==0 for c in certs)
mods=sum(len(c['modules']) for c in certs);queries=sum(len(c['queries']) for c in certs)
ths=sum(len(c['theoremRegistrations']) for c in certs);defs=sum(len(c['constructionRegistrations']) for c in certs)
checks=sum(c['exhaustiveTheorems'] for c in certs);edges=sum(c['requiredProofValueEdges'] for c in certs)
assert (mods,queries,ths,defs,checks,edges)==(26,102,77,25,185,144)
routefile='gamma-one-arithmetic-geometry-promotion-route-626.json'
archive='Tools/gamma-one-arithmetic-geometry-20261026-626'
dependency='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero Galois association -> arithmetic realization of original finite Gamma1 Hecke characters -> geometric/H1 comparison retaining the original homogeneous coefficient action, and diamond comparison -> actual Gamma1 finite fields, Picard correspondence and arithmetic Hecke equivariance.'
discharged='The actual Gamma1 and Hecke function fields are finite over the original transcendental j coordinate, including after Laurent scalar extension. Native modular norms, original level-one j polynomials, Laurent independence and primitive elements derive rational polynomial relations and finite degree. Native modular translation and existing sparse sums prove the integral expansion of the actual form f(dz); literal q-substitution therefore defines the second Hecke field map. Both field maps are finite by existing coordinate exchange. Their proved closed constant residues and existing divisor norm/degree identities construct the actual Picard Hecke operator. Coefficient transport preserves the same fields, fixes original j under arithmetic automorphisms, and commutes with both maps. The genuine arithmetic place action preserves normalized order, degree and principal divisors; native quotient functoriality gives the actual Gamma1 Picard Galois action and its torsion stability. Place restriction and ramification identities prove that this action commutes with the actual Picard Hecke operator. No finite-coordinate, field-preservation, finite-map, residue-degree, degree/principal-preservation or arithmetic-equivariance premise remains.'
boundary='The geometric/H1 comparison must retain the original homogeneous matrix coefficient action and prove the upper/lower correspondence and transpose/diamond conventions. Arithmetic equivariance of the ordinary Picard operator alone does not identify the original binary-coefficient finite Hecke characters with geometric characters. Diamond comparison, Frobenius/inertia, arithmetic Galois realization of these finite characters, original all-weight characteristic-zero association, required local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain required. No characteristic-zero character lift or deformation point is inferred. 16/20; DUB-17--20 OPEN.'
route='Renewed primary inspection selects actual Gamma1 integral-ratio and finite-coordinate arguments from the frozen Anthropic snapshot. Its inspected adic theorem still requires a characteristic-zero Hecke-and-diamond character; the separate Gamma0 result is residual over a field. Reuse original j, native modular norms, existing level-one polynomials, Laurent independence, scalar-extension finiteness, native modular translation, original dilation and sparse sums. Existing coordinate exchange, closed residues, divisor norm/degree formulas, inverse-coefficient place transport and quotient action laws supply the full Picard/arithmetic construction. External alternate coordinates, duplicate cusp/scalar-extension development, conditional fallback maps and an abstract semilinear framework are deferred. Explicit inclusion projection and composition avoid kernel/rewrite unfolding without changing limits. Missing docstrings and construction-root dependency accounting have fresh audits; all failed evidence is preserved. Root pins and full source contracts are unchanged.'
status='The actual Gamma1 finite-field, Picard and arithmetic-Hecke chain passes 185 exhaustive scratch checks and 102 explicit public axiom queries across 26 modules, with sixteen linters per module and zero diagnostics. Four declaration-value audits verify 144 required dependencies. Production aggregate, focused audit and sequential foundation/paper verification of the 8,316-module scope are pending.'
def output(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output(routefile,json.dumps(dict(scope=626,scopeIds=[i for i,_,_ in spec],receipts=digests,dependency=dependency,discharged=discharged,remaining=boundary,route=route,precedingCanonicalScope=8290,rootPinsChanged=False,proofLimitsChanged=False,externalImport=False,fullGoal='16/20; DUB-17--20 OPEN; all 20 acceptance gates unchanged.',reason='Require preceding canonical PASS and immutable archive before production mutation.'),indent=2)+'\n')
repl={
'primitive-gamma-one-hecke-promotion-route-618.json':routefile,
'Tools/primitive-gamma-one-hecke-20261026-618':archive,
'Tools/gamma-one-hecke-trace-20261025-599':'Tools/primitive-gamma-one-hecke-20261026-618',
'appliedSourcePrimitiveGammaOneHeckeRealization':'appliedSourceGammaOneArithmeticGeometry',
'appliedSourceGammaOneHeckeTrace':'appliedSourcePrimitiveGammaOneHeckeRealization',
'SourcePrimitiveGammaOneHeckeRealization':'SourceGammaOneArithmeticGeometry',
'primitive_gamma_one_hecke_realization':'gamma_one_arithmetic_geometry',
'source-primitive-gamma-one-hecke-realization':'source-gamma-one-arithmetic-geometry',
'SOURCE PRIMITIVE GAMMA ONE HECKE REALIZATION':'SOURCE GAMMA ONE ARITHMETIC GEOMETRY',
'actual Gamma1 transfer and original-form finite characters':'actual Gamma1 arithmetic geometry and Hecke equivariance',
'Actual Gamma1 transfer and original-form finite characters':'Actual Gamma1 arithmetic geometry and Hecke equivariance',
'8,290':'8,316','8,274':'8,290','8290':'8316','8274':'8290'}
rx=re.compile('|'.join(map(re.escape,sorted(repl,key=len,reverse=True))))
tr=lambda s:rx.sub(lambda m:repl[m[0]],s)
s=tr((p/'integrate_source_primitive_gamma_one_hecke_realization_8290.py').read_text(encoding='utf-8'))
s=re.sub(r'^digests = .+$',lambda _:'digests = '+repr(digests),s,flags=re.M)
s=s.replace('(16, 16, 41, 30, 11)','(26, 26, 102, 77, 25)').replace('count == 110','count == 185').replace('"increment": 16, "queries": 41','"increment": 26, "queries": 102')
for k,v in [('dependency',dependency),('discharged',discharged),('boundary',boundary),('route',route),('status',status)]:
 s=re.sub(r'^'+k+r' = .+$',lambda _,k=k,v=v:k+' = '+repr(v),s,flags=re.M)
a=s.index('evidence=[p/');b=s.index("for cert in certs:\n    evidence.append",a)
evidence=[n for _,n,_ in spec]+[n for _,_,n in spec]+['gamma-one-finite-fields-promotion-route-623.json','gamma-one-finite-fields-preexecution-review-8305.json','prepare_gamma_one_finite_fields_promotion_8305.py']
for c in certs:
 for field in ['log','dependencyAuditLog']:
  evidence += [Path(c[field]).with_suffix(x).name for x in ['.lean','.log','.exit']]
for i in [619,620,621,622,624,625]:
 evidence += [f.name for f in p.iterdir() if f.is_file() and f.suffix in ['.py','.json','.txt'] and re.search(r'(?<!\d)'+str(i)+r'[a-z]?(?:\.|-)',f.name)]
for _,name,_ in spec:evidence.append(name.replace('-scratch-receipt.json','-audit-config.json'))
for n in ['SourceGammaOneHeckePicardAudit2.lean','SourceGammaOneHeckePicardAudit2.log','SourceGammaOneHeckePicardAudit2.exit','SourceGammaOneHeckePicardDependencyAudit2.lean','SourceGammaOneHeckePicardDependencyAudit2.log','SourceGammaOneHeckePicardDependencyAudit2.exit','source-gamma-one-hecke-picard-2-audit-config.json','SourceGammaOneFunctionFieldAudit10.lean','SourceGammaOneFunctionFieldAudit10.log','SourceGammaOneFunctionFieldAudit10.exit','SourceGammaOneFunctionFieldDependencyAudit10.lean','source-gamma-one-function-field-10-audit-config.json']:
 assert (p/n).exists();evidence.append(n)
folders=['gamma1-function-field-620-before-definition-docstrings','gamma1-hecke-fields-622-before-explicit-inclusion-projection','gamma1-geometric-reuse-619','gamma1-hecke-correspondence-reuse-621']
s=s[:a]+'evidence=[p/'+repr(routefile)+']\nevidence += [p/n for n in '+repr(sorted(set(evidence)))+']\nfor folder in '+repr(folders)+':\n    evidence += sorted(f for f in (p/folder).rglob("*") if f.is_file())\n'+s[b:]
s=s.replace("target=r/archive_rel/(source.parent.name if source.parent != p else '')/(source.name+('.txt' if source.suffix=='.lean' else ''))","target=r/archive_rel/source.relative_to(p)\n    if source.suffix=='.lean':target=target.with_name(target.name+'.txt')")
oldedge='  PRIMITIVEGAMMAONE8290["Actual surjective Gamma1 transfer/Hecke compatibility and original Fourier-valued finite Gamma1 operator characters proved; arithmetic geometric and diamond comparison, Galois realization and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
newedge='  PRIMITIVEGAMMAONE8290["Actual surjective Gamma1 transfer/Hecke compatibility and original Fourier-valued finite Gamma1 operator characters (DUB-17/18)"] --> GAMMAONEFIELDS8316\n  GAMMAONEFIELDS8316["Actual Gamma1 fields, finite maps, Picard Hecke and arithmetic equivariance proved. Original homogeneous-coefficient H1/diamond comparison, Frobenius/inertia, all-weight Galois realization and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
s=re.sub(r'^edge = .+$',lambda _:'edge = '+repr(oldedge),s,flags=re.M)
s=re.sub(r'^arch.write_text\(.*$',lambda _:"arch.write_text(arch.read_text(encoding='utf-8').replace(edge,"+repr(newedge)+"),encoding='utf-8')",s,flags=re.M)
s=re.sub(r'^    "promotionChanges": .+$',lambda _:'    "promotionChanges": '+repr('Only scratch imports are qualified. Every audited statement, proof body and comment is preserved. Actual modular forms, original j, integral expansions, literal Laurent fields and both finite field maps retain their definitions. No source contract is weakened.')+',',s,flags=re.M)
a=s.index("    '  logInfo m!");b=s.index("', b)",a)
s=s[:a]+'    \'  logInfo m!"SOURCE GAMMA ONE ARITHMETIC GEOMETRY AUDIT PASS: {count} theorems including private/generated declarations. Actual Gamma1 fields and finite maps construct the genuine Picard Hecke operator and arithmetic action; their Hecke equivariance and torsion stability are proved. Original homogeneous-coefficient H1/diamond comparison, Frobenius/inertia, all-weight association and higher continuation remain open; 16/20 gates."\\n'+s[b:]
output('integrate_source_gamma_one_arithmetic_geometry_8316.py',s)
for stem in ['prepare_primitive_gamma_one_hecke_realization_production_ownership','prepare_primitive_gamma_one_hecke_realization_scratch_ownership','compare_primitive_gamma_one_hecke_realization_ownership','prepare_primitive_gamma_one_hecke_realization_global_ownership']:
 s=tr((p/(stem+'_8290.py')).read_text(encoding='utf-8'))
 s=re.sub(r'\b110\b','185',s).replace('All 16 mathematical','All 26 mathematical').replace('len(names)==len(certs)==6','len(names)==len(certs)==4')
 output(tr(stem+'_8290.py'),s)
s=tr((p/'record_source_primitive_gamma_one_hecke_realization_8290.py').read_text(encoding='utf-8'))
s=re.sub(r'\b110\b','185',s)
s=s.replace('t.count("All linting checks passed!") == 16','t.count("All linting checks passed!") == 26').replace('len(k["modules"]) == 16','len(k["modules"]) == 26')
s=s.replace('"incrementModules": 16','"incrementModules": 26').replace('"linterScopes": 16','"linterScopes": 26')
s=s.replace('len(ownershipComparison["scopes"]) == 6','len(ownershipComparison["scopes"]) == 4')
s=s.replace('Six declaration-value audits verify 78 required dependencies.','Four declaration-value audits verify 144 required dependencies.').replace('int(a[2]) == 23874','int(a[2]) == 23951')
output('record_source_gamma_one_arithmetic_geometry_8316.py',s)
for stem in ['build_primitive_gamma_one_hecke_realization','verify_primitive_gamma_one_hecke_realization']:
 output(tr(stem+'_8290.ps1'),tr((p/(stem+'_8290.ps1')).read_text(encoding='utf-8')))
output('archive_gamma_one_arithmetic_geometry_canonical_8316.py',tr((p/'archive_primitive_gamma_one_hecke_realization_canonical_8290.py').read_text(encoding='utf-8')))
scripts=[f for f in p.iterdir() if re.search(r'8316\.(py|ps1)$',f.name) and f.name!='prepare_gamma_one_arithmetic_geometry_promotion_8316.py']
for f in scripts:
 t=f.read_text(encoding='utf-8')
 if f.suffix=='.py':ast.parse(t)
 assert '16/22' not in t and 'DUB-17-22' not in t,f
review=dict(status='Prepared; require 8290 canonical PASS and immutable archive before integration.',route=routefile,routeSha256=sha(p/routefile),modules=mods,queries=queries,theorems=ths,constructions=defs,exhaustiveScratchChecks=checks,proofValueEdges=edges,scopes=4,receipts=digests,expectedConsumers=23951,expectedConstructions=2313,fullGoal='16/20; DUB-17--20 OPEN; all 20 gates unchanged.',sourceBodies='Audited statements, bodies and comments unchanged; only scratch project imports qualified.',scripts=[dict(path=str(f),sha256=sha(f)) for f in scripts],productionMutation=False)
output('gamma-one-arithmetic-geometry-preexecution-review-8316.json',json.dumps(review,indent=2)+'\n')
print(json.dumps(dict(scripts=len(scripts),modules=mods,queries=queries,exhaustive=checks,edges=edges,productionMutation=False)))
