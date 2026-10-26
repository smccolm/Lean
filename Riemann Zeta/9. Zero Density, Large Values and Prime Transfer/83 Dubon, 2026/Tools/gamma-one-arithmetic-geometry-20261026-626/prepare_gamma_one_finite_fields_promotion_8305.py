from pathlib import Path
import ast,json,re,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
spec=[('620b','source-gamma-one-function-field-10b-scratch-receipt.json','gamma1-function-field-finite-route-620b.json'),('622','source-gamma-one-hecke-field-5-scratch-receipt.json','gamma1-finite-hecke-field-route-622.json')]
certs=[json.loads((p/n).read_text()) for _,n,_ in spec]
digests={n:sha(p/n) for _,n,_ in spec}
assert all(c['exit']==c['diagnostics']==0 for c in certs)
mods=sum(len(c['modules']) for c in certs);queries=sum(len(c['queries']) for c in certs)
ths=sum(len(c['theoremRegistrations']) for c in certs);defs=sum(len(c['constructionRegistrations']) for c in certs)
checks=sum(c['exhaustiveTheorems'] for c in certs);edges=sum(c['requiredProofValueEdges'] for c in certs)
assert (mods,queries,ths,defs,checks,edges)==(15,54,41,13,87,73)
routefile='gamma-one-finite-fields-promotion-route-623.json'
archive='Tools/gamma-one-finite-fields-20261026-623'
dependency='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero Galois association -> arithmetic realization of original finite Gamma1 Hecke characters -> genuine finite geometric Gamma1 Hecke correspondences -> actual integral-ratio function fields and both literal finite field maps.'
discharged='The actual rational Gamma1 integral-ratio field and the Gamma1-intersection-Gamma0 Hecke field are finite over the original transcendental j coordinate, also after Laurent scalar extension. Native modular norms, the proved level-one j polynomial theorem and Laurent coefficient independence give bounded rational polynomial relations; native primitive-element theory proves finite dimension. Existing scalar-extension finiteness transports this result without a new coordinate. The actual translated form f(dz) has the sparse Fourier expansion and retains integral coefficients. The literal substitution q to q^d therefore maps the Gamma1 field into the Hecke field. Both scalar-extended Hecke maps, inclusion and substitution, are constructed and proved finite. No finite-coordinate, field-preservation, modular-polynomial symmetry or finite-map premise remains.'
boundary='Arithmetic geometric/H1 and diamond comparison, geometric Galois realization of the original finite characters, original all-weight characteristic-zero association, required local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain required. Finiteness of actual function fields and correspondences does not supply a characteristic-zero Hecke character or deformation point. 16/20; DUB-17--20 OPEN.'
route='Renewed primary-source inspection selects the Gamma1 integral-ratio and finite-coordinate arguments from the frozen Anthropic snapshot. The exact inspected Galois theorem still accepts characteristic-zero Hecke-and-diamond characters; the separate Gamma0 theorem is residual over a field, not a higher-precision Gamma1 realization. Reuse the existing original j, modular norms, level-one polynomial theorem, Laurent independence and scalar-extension degree transport. Native ModularForm.translate, the original dilation matrix, existing sparse sums and coefficient-reindex compatibility shorten the second field map. Existing finite-coordinate exchange proves its finiteness. The external alternate coordinate, duplicate scalar-extension/cusp developments and conditional fallback map are deferred. One kernel reflexivity timeout is repaired by the native inclusion projection theorem; seven missing definition docstrings are repaired with fresh audits. All failed evidence is preserved; limits and pins are unchanged.'
status='The actual Gamma1 finite-coordinate and finite-Hecke-field chain passes 87 exhaustive scratch checks and 54 explicit axiom queries across 15 modules, with sixteen linters per module and zero diagnostics. Two declaration-value audits verify 73 required dependencies. Production aggregate, focused audit and sequential foundation/paper verification of the 8,305-module scope are pending.'
def output(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output(routefile,json.dumps(dict(scope=623,scopeIds=[i for i,_,_ in spec],receipts=digests,dependency=dependency,discharged=discharged,remaining=boundary,route=route,precedingCanonicalScope=8290,rootPinsChanged=False,proofLimitsChanged=False,externalImport=False,fullGoal='16/20; DUB-17--20 OPEN; all 20 acceptance gates unchanged.',reason='Require preceding canonical PASS and immutable archive before production mutation.'),indent=2)+'\n')
repl={
'primitive-gamma-one-hecke-promotion-route-618.json':routefile,
'Tools/primitive-gamma-one-hecke-20261026-618':archive,
'Tools/gamma-one-hecke-trace-20261025-599':'Tools/primitive-gamma-one-hecke-20261026-618',
'appliedSourcePrimitiveGammaOneHeckeRealization':'appliedSourceGammaOneFiniteFields',
'appliedSourceGammaOneHeckeTrace':'appliedSourcePrimitiveGammaOneHeckeRealization',
'SourcePrimitiveGammaOneHeckeRealization':'SourceGammaOneFiniteFields',
'primitive_gamma_one_hecke_realization':'gamma_one_finite_fields',
'source-primitive-gamma-one-hecke-realization':'source-gamma-one-finite-fields',
'SOURCE PRIMITIVE GAMMA ONE HECKE REALIZATION':'SOURCE GAMMA ONE FINITE FIELDS',
'actual Gamma1 transfer and original-form finite characters':'actual Gamma1 finite coordinates and finite Hecke field maps',
'Actual Gamma1 transfer and original-form finite characters':'Actual Gamma1 finite coordinates and finite Hecke field maps',
'8,290':'8,305','8,274':'8,290','8290':'8305','8274':'8290'}
rx=re.compile('|'.join(map(re.escape,sorted(repl,key=len,reverse=True))))
tr=lambda s:rx.sub(lambda m:repl[m[0]],s)
s=tr((p/'integrate_source_primitive_gamma_one_hecke_realization_8290.py').read_text(encoding='utf-8'))
s=re.sub(r'^digests = .+$',lambda _:'digests = '+repr(digests),s,flags=re.M)
s=s.replace('(16, 16, 41, 30, 11)','(15, 15, 54, 41, 13)').replace('count == 110','count == 87').replace('"increment": 16, "queries": 41','"increment": 15, "queries": 54')
for k,v in [('dependency',dependency),('discharged',discharged),('boundary',boundary),('route',route),('status',status)]:
 s=re.sub(r'^'+k+r' = .+$',lambda _,k=k,v=v:k+' = '+repr(v),s,flags=re.M)
a=s.index('evidence=[p/');b=s.index("for cert in certs:\n    evidence.append",a)
evidence=[n for _,n,_ in spec]+[n for _,_,n in spec]
for c in certs:
 for field in ['log','dependencyAuditLog']:
  evidence += [Path(c[field]).with_suffix(x).name for x in ['.lean','.log','.exit']]
for i in [619,620,621,622]:
 evidence += [f.name for f in p.iterdir() if f.is_file() and f.suffix in ['.py','.json','.txt'] and re.search(r'(?<!\d)'+str(i)+r'[a-z]?(?:\.|-)',f.name)]
for _,name,_ in spec:evidence.append(name.replace('-scratch-receipt.json','-audit-config.json'))
for n in ['SourceGammaOneFunctionFieldAudit10.lean','SourceGammaOneFunctionFieldAudit10.log','SourceGammaOneFunctionFieldAudit10.exit','SourceGammaOneFunctionFieldDependencyAudit10.lean','source-gamma-one-function-field-10-audit-config.json']:
 assert (p/n).exists();evidence.append(n)
folders=['gamma1-function-field-620-before-definition-docstrings','gamma1-hecke-fields-622-before-explicit-inclusion-projection','gamma1-geometric-reuse-619','gamma1-hecke-correspondence-reuse-621']
s=s[:a]+'evidence=[p/'+repr(routefile)+']\nevidence += [p/n for n in '+repr(sorted(set(evidence)))+']\nfor folder in '+repr(folders)+':\n    evidence += sorted(f for f in (p/folder).rglob("*") if f.is_file())\n'+s[b:]
s=s.replace("target=r/archive_rel/(source.parent.name if source.parent != p else '')/(source.name+('.txt' if source.suffix=='.lean' else ''))","target=r/archive_rel/source.relative_to(p)\n    if source.suffix=='.lean':target=target.with_name(target.name+'.txt')")
oldedge='  PRIMITIVEGAMMAONE8290["Actual surjective Gamma1 transfer/Hecke compatibility and original Fourier-valued finite Gamma1 operator characters proved; arithmetic geometric and diamond comparison, Galois realization and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
newedge='  PRIMITIVEGAMMAONE8290["Actual surjective Gamma1 transfer/Hecke compatibility and original Fourier-valued finite Gamma1 operator characters (DUB-17/18)"] --> GAMMAONEFIELDS8305\n  GAMMAONEFIELDS8305["Actual Gamma1/Hecke fields finite over original j; both literal scalar-extended Hecke maps finite. Arithmetic geometric/H1 and diamond comparison, Galois realization and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
s=re.sub(r'^edge = .+$',lambda _:'edge = '+repr(oldedge),s,flags=re.M)
s=re.sub(r'^arch.write_text\(.*$',lambda _:"arch.write_text(arch.read_text(encoding='utf-8').replace(edge,"+repr(newedge)+"),encoding='utf-8')",s,flags=re.M)
s=re.sub(r'^    "promotionChanges": .+$',lambda _:'    "promotionChanges": '+repr('Only scratch imports are qualified. Every audited statement, proof body and comment is preserved. Actual modular forms, original j, integral expansions, literal Laurent fields and both finite field maps retain their definitions. No source contract is weakened.')+',',s,flags=re.M)
a=s.index("    '  logInfo m!");b=s.index("', b)",a)
s=s[:a]+'    \'  logInfo m!"SOURCE GAMMA ONE FINITE FIELDS AUDIT PASS: {count} theorems including private/generated declarations. Actual Gamma1 and Hecke function fields are finite over original j, and both literal scalar-extended Hecke field maps are finite. Arithmetic geometric/H1 and diamond comparison, Galois realization, original all-weight association and higher continuation remain open; 16/20 gates."\\n'+s[b:]
output('integrate_source_gamma_one_finite_fields_8305.py',s)
for stem in ['prepare_primitive_gamma_one_hecke_realization_production_ownership','prepare_primitive_gamma_one_hecke_realization_scratch_ownership','compare_primitive_gamma_one_hecke_realization_ownership','prepare_primitive_gamma_one_hecke_realization_global_ownership']:
 s=tr((p/(stem+'_8290.py')).read_text(encoding='utf-8'))
 s=re.sub(r'\b110\b','87',s).replace('All 16 mathematical','All 15 mathematical').replace('len(names)==len(certs)==6','len(names)==len(certs)==2')
 output(tr(stem+'_8290.py'),s)
s=tr((p/'record_source_primitive_gamma_one_hecke_realization_8290.py').read_text(encoding='utf-8'))
s=re.sub(r'\b110\b','87',s)
s=s.replace('t.count("All linting checks passed!") == 16','t.count("All linting checks passed!") == 15').replace('len(k["modules"]) == 16','len(k["modules"]) == 15')
s=s.replace('"incrementModules": 16','"incrementModules": 15').replace('"linterScopes": 16','"linterScopes": 15')
s=s.replace('len(ownershipComparison["scopes"]) == 6','len(ownershipComparison["scopes"]) == 2')
s=s.replace('Six declaration-value audits verify 78 required dependencies.','Two declaration-value audits verify 73 required dependencies.').replace('int(a[2]) == 23874','int(a[2]) == 23915')
output('record_source_gamma_one_finite_fields_8305.py',s)
for stem in ['build_primitive_gamma_one_hecke_realization','verify_primitive_gamma_one_hecke_realization']:
 output(tr(stem+'_8290.ps1'),tr((p/(stem+'_8290.ps1')).read_text(encoding='utf-8')))
output('archive_gamma_one_finite_fields_canonical_8305.py',tr((p/'archive_primitive_gamma_one_hecke_realization_canonical_8290.py').read_text(encoding='utf-8')))
scripts=[f for f in p.iterdir() if re.search(r'8305\.(py|ps1)$',f.name) and f.name!='prepare_gamma_one_finite_fields_promotion_8305.py']
for f in scripts:
 t=f.read_text(encoding='utf-8')
 if f.suffix=='.py':ast.parse(t)
 assert '16/22' not in t and 'DUB-17-22' not in t,f
review=dict(status='Prepared; require 8290 canonical PASS and immutable archive before integration.',route=routefile,routeSha256=sha(p/routefile),modules=mods,queries=queries,theorems=ths,constructions=defs,exhaustiveScratchChecks=checks,proofValueEdges=edges,scopes=2,receipts=digests,expectedConsumers=23915,expectedConstructions=2301,fullGoal='16/20; DUB-17--20 OPEN; all 20 gates unchanged.',sourceBodies='Audited statements, bodies and comments unchanged; only scratch project imports qualified.',scripts=[dict(path=str(f),sha256=sha(f)) for f in scripts],productionMutation=False)
output('gamma-one-finite-fields-preexecution-review-8305.json',json.dumps(review,indent=2)+'\n')
print(json.dumps(dict(scripts=len(scripts),modules=mods,queries=queries,exhaustive=checks,edges=edges,productionMutation=False)))
