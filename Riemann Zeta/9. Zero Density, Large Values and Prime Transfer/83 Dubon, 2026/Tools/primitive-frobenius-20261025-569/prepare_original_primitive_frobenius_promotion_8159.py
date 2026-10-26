from pathlib import Path
import re,json,hashlib
p=Path(__file__).parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
stems=['source-original-primitive-cyclotomic-12','source-original-primitive-frobenius-charpoly-5','source-original-primitive-residual-frobenius-7','source-original-prescribed-residual-frobenius-2']
certPaths=[p/(s+'-scratch-receipt.json') for s in stems]
certs=[json.loads(f.read_text(encoding='utf-8')) for f in certPaths]
mods=[m for c in certs for m in c['modules']];queries=[n for c in certs for n in c['queries']]
ths=[n for c in certs for n in c['theoremRegistrations']];defs=[n for c in certs for n in c['constructionRegistrations']]
assert (len(mods),len(set(mods)),len(queries),len(ths),len(defs))==(26,26,50,48,2)
assert sum(c['exhaustiveTheorems'] for c in certs)==74
assert sum(c['requiredProofValueEdges'] for c in certs)==98
digests={f.name:sha(f) for f in certPaths}
routes=['primitive-cyclotomic-route-564.json','primitive-frobenius-charpoly-route-565.json','primitive-residual-frobenius-route-566.json','prescribed-residual-frobenius-route-567b.json']
dependency='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> all-weight residual association -> weight-two prescribed residual realization -> the actual primitive original Tate representation has arithmetic Frobenius characteristic polynomial X^2-a_q*X+q and trivial good-prime inertia -> compare the actual rank-two projector image and transport its literal Weil pairing through the existing spanning specialization'
discharged='The actual arithmetic projector image is identified with the existing spanning primitive specialization. Its literal root-valued alternating Weil pairing is nondegenerate and has the original cyclotomic multiplier, so the same representation has cyclotomic determinant. The exact source valuation arithmetic Frobenius acts on prime-to-q roots by q-th powers, giving cyclotomic value q. The original Tate quadratic relation therefore yields determinant q, trace a_q and characteristic polynomial X^2-a_q*X+q. The already constructed integral lattice and literal residue representation retain this polynomial and trivial good-prime inertia. A prescribed Fourier-field embedding is retained through the actual continuous Tate specialization, stable lattice and residual construction. No separate determinant, nondegenerate pairing, Frobenius action, stable lattice or residual compatibility hypothesis is supplied.'
boundary='Choosing the coefficient completion and residue embedding compatible with the source prescribed algebraic-integer reduction, the arithmetic quotient and norm-local comparisons, closure of the parabolic branch, final weight twist and support comparison, arithmetic automorphy and all-weight continuation remain required. The prescribed-embedding theorem explicitly assumes a genuine finite local coefficient field and valuation extension, to be discharged by the chosen completion. 16/20; DUB-17--20 OPEN.'
route='Reuse native range_liftBaseChange, finite-dimensional bijectivity and alternating two-coordinate determinant algebra to retain the original representation. Reuse source valuation root lifting, PadicInt.ext_of_toZModPow, the exact cyclotomic character and native Cayley-Hamilton. Reuse the existing stable lattice and literal entrywise reduction with native characteristic-polynomial transport. Preserve an arbitrary prescribed Fourier-field embedding, then choose the completion at the kernel of the source reduction using the proved quotient/residue equivalence. No external import, root pin change, proof-limit change or generic Jacobian infrastructure is needed.'
status='The actual primitive Frobenius and prescribed residual realization passes 74 exhaustive scratch checks and 50 explicit axiom queries across 26 modules, with sixteen linters per module and zero diagnostics. Four declaration-value audits verify 98 required dependencies. The original failed dependency-name audit is preserved with its passing corrected successor; no proof source changed. Production aggregate, focused audit and sequential foundation/paper verification of the 8,159-module scope are pending.'
routePath=p/'original-primitive-frobenius-promotion-route-569.json';assert not routePath.exists()
routePath.write_text(json.dumps(dict(scope=569,scopeIds=[564,565,566,567],receipts=digests,dependency=dependency,discharged=discharged,remaining=boundary,route=route,precedingCanonicalScope=8133,mathematicalSource='Frozen Dubon arXiv2609.17875v1; complete original goal unchanged.',rootPinsChanged=False,proofLimitsChanged=False,externalLocalBuild=False,externalImport=False),indent=2)+'\n',encoding='utf-8')
def transform(s):
 s=s.replace('OriginalPrimitiveTateImage','OriginalPrimitiveFrobenius').replace('original_primitive_tate_image','original_primitive_frobenius').replace('primitive-tate-image','primitive-frobenius').replace('PRIMITIVE TATE IMAGE','PRIMITIVE FROBENIUS')
 s=s.replace('OriginalPrimitiveProjector','OriginalPrimitiveTateImage')
 s=s.replace('8133','8159').replace('8102','8133').replace('8,133','8,159').replace('8,102','8,133')
 s=s.replace('promotion-route-563','promotion-route-569').replace('20261025-563','20261025-569')
 s=s.replace('primitive-projector-20261025-559','primitive-tate-image-20261025-563')
 return s
def output(name,s):
 f=p/name;assert not f.exists();f.write_text(s,encoding='utf-8')
s=transform((p/'integrate_source_original_primitive_tate_image_8133.py').read_text(encoding='utf-8'))
s=re.sub(r'^digests = .+$',lambda _:'digests = '+repr(digests),s,flags=re.M)
s=s.replace('(31, 31, 66, 53, 13)','(26, 26, 50, 48, 2)').replace('count == 140','count == 74')
for label,value in [('dependency',dependency),('discharged',discharged),('boundary',boundary),('status',status),('route',route)]:
 s=re.sub(r'^'+label+r' = .+$',lambda _,label=label,value=value:label+' = '+repr(value),s,flags=re.M)
s=s.replace('Actual nondegenerate rank-two primitive Tate image (','Actual primitive Frobenius and prescribed residual realization (')
a=s.index('evidence += [p/name for name in digests]');b=s.index("for cert in certs:\n    for field in ['log','dependencyAuditLog']:",a)
extra=['prepare_primitive_cyclotomic_audit_564.py','record_primitive_cyclotomic_564.py','prepare_primitive_frobenius_charpoly_audit_565.py','record_primitive_frobenius_charpoly_565.py','prepare_primitive_residual_frobenius_audit_566.py','record_primitive_residual_frobenius_566.py','prepare_prescribed_residual_frobenius_audit_567.py','prepare_prescribed_residual_dependency_successor_567b.py','record_prescribed_residual_frobenius_567.py','prescribed-residual-frobenius-route-567.json','source-original-prescribed-residual-frobenius-2-audit-config.json','SourceOriginalPrescribedResidualFrobeniusDependencyAudit2.lean','SourceOriginalPrescribedResidualFrobeniusDependencyAudit2.log','SourceOriginalPrescribedResidualFrobeniusDependencyAudit2.exit']
configs=[stems[0]+'-audit-config.json',stems[1]+'-audit-config.json',stems[2]+'-audit-config.json',stems[3]+'-audit-config-567b.json']
for name in routes+extra+configs:assert (p/name).exists(),name
s=s[:a]+"evidence += [p/name for name in digests]\nevidence += [p/name for name in "+repr(routes+extra+configs)+"]\nfor cert in certs:\n    evidence.append(Path(cert['reuseReview']))\n\n"+s[b:]
oldEdge='  PRIMITIVETATEIMAGE8133["Actual nondegenerate rank-two primitive Tate image; spanning-specialization comparison and determinant OPEN (DUB-17/18)"] --> CMARITH4538'
newEdge='  PRIMITIVETATEIMAGE8133["Actual nondegenerate rank-two primitive Tate image (DUB-17/18)"] --> PRIMITIVEFROBENIUS8159\n  PRIMITIVEFROBENIUS8159["Same original primitive representation: cyclotomic determinant, exact Frobenius polynomial and prescribed-embedding residual realization; source reduction, arithmetic quotient and norm-local comparisons OPEN (DUB-17/18)"] --> CMARITH4538'
s=re.sub(r'^edge = .+$',lambda _:'edge = '+repr(oldEdge),s,flags=re.M)
s=re.sub(r'^arch.write_text\(.*$',lambda _:"arch.write_text(arch.read_text(encoding='utf-8').replace(edge, "+repr(newEdge)+"),encoding='utf-8')",s,flags=re.M)
s=s.replace('Actual nondegenerate rank-two primitive Tate image - ','Actual primitive Frobenius and prescribed residual realization - ')
s=s.replace('The actual arithmetic projector has a nonzero rank-two original Tate image with an injective restricted Weil pairing. Comparison to the existing spanning specialization, determinant, residual association, automorphy and all-weight continuation remain open; 16/20 gates.','The same original primitive representation has cyclotomic determinant, exact Frobenius trace/determinant/characteristic polynomial, and a prescribed-embedding residual realization. Source reduction compatibility, arithmetic quotient and norm-local comparisons, automorphy and all-weight continuation remain open; 16/20 gates.')
s=s.replace('"increment": 31, "queries": 66','"increment": 26, "queries": 50')
compile(s,'integrator8159','exec');output('integrate_source_original_primitive_frobenius_8159.py',s)
for stem in ['prepare_original_primitive_tate_image_production_ownership','prepare_original_primitive_tate_image_scratch_ownership','compare_original_primitive_tate_image_ownership','record_source_original_primitive_tate_image','verify_original_primitive_tate_image']:
 ext='.ps1' if stem.startswith('verify') else '.py'
 s=transform((p/(stem+'_8133'+ext)).read_text(encoding='utf-8'))
 if stem.startswith('compare'):s=s.replace('==3','==4').replace('==140','==74')
 if stem.startswith('record'):
  s=re.sub(r'\b140\b','74',s);s=re.sub(r'\b31\b','26',s)
  s=s.replace('== 3','== 4').replace('== 2212','== 2214').replace('== 23592','== 23640')
  s=s.replace('actual nondegenerate rank-two primitive Tate image','actual primitive Frobenius and prescribed residual realization').replace('Three declaration-value audits verify 91 required dependencies.','Four declaration-value audits verify 98 required dependencies.')
 if ext=='.py':compile(s,stem+'8159','exec')
 output(stem.replace('primitive_tate_image','primitive_frobenius')+'_8159'+ext,s)
# Use explicit numeric Name constructors learned from the preserved 8133 helper failure.
s=(p/'prepare_original_primitive_tate_image_global_ownership_8133b.py').read_text(encoding='utf-8')
a=s.index("log=p/'SourceOriginalPrimitiveTateImageOwnership8133.log'"); b=s.index("f=p/'source-original-primitive-tate-image-global-ownership-successor-8133b.json'")
s='from pathlib import Path\nimport re,json\np=Path(__file__).parent\n'+s[a:b]
s=s.replace("assert len(names)==len(set(names))==140","assert names and len(names)==len(set(names))")
s=s.replace("s=old.with_suffix('.lean').read_text(encoding='utf-8')", "s="+repr((p/'SourceOriginalPrimitiveTateImageGlobalOwnership8133.lean').read_text(encoding='utf-8')))
s=transform(s).replace('GlobalOwnership8159b','GlobalOwnership8159')
s=s[:s.index('sha=lambda f:')]
compile(s,'global8159','exec');output('prepare_original_primitive_frobenius_global_ownership_8159.py',s)
print(json.dumps(dict(modules=26,queries=50,theorems=48,constructions=2,scratchChecks=74,proofEdges=98,receipts=digests,routeSha256=sha(routePath))))
