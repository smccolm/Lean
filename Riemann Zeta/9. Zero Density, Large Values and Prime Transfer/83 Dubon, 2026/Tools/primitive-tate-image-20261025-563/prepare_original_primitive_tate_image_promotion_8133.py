from pathlib import Path
import re,json,hashlib
p=Path(__file__).parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
stems=['source-original-coefficient-weil-6','source-original-primitive-tate-restriction-8','source-original-primitive-rank-two-17']
certPaths=[p/(s+'-scratch-receipt.json') for s in stems]
certs=[json.loads(f.read_text(encoding='utf-8')) for f in certPaths]
mods=[m for c in certs for m in c['modules']];queries=[n for c in certs for n in c['queries']]
ths=[n for c in certs for n in c['theoremRegistrations']];defs=[n for c in certs for n in c['constructionRegistrations']]
assert (len(mods),len(set(mods)),len(queries),len(ths),len(defs))==(31,31,66,53,13)
assert sum(c['exhaustiveTheorems'] for c in certs)==140
assert sum(c['requiredProofValueEdges'] for c in certs)==91
digests={f.name:sha(f) for f in certPaths}
routes=['coefficient-weil-route-560.json','primitive-tate-restriction-route-561.json','primitive-rank-two-route-562b.json']
dependency='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> residual association -> primitive Frobenius determinant -> nonzero required primitive component pairing -> nondegenerate rank-two image of the actual arithmetic projector on the original coefficient-extended Tate module'
discharged='The original rational Weil pairing remains injective after extension to the actual coefficient field, with its alternating, good-prime Hecke adjointness and cyclotomic multiplier identities. The proved integral cusp/lattice relations factor the actual original Tate action through the same integral Hecke algebra used by the arithmetic projector. Literal coefficient extension preserves its prime operators and polynomial, so the actual projected operator is idempotent and self-adjoint. Existing all-word original rank-two Tate coordinates and native finite-product scalar extension identify its image: the prescribed p-adic Hecke character has value one on the projector and gives its scalar action, making the actual image rank two. The same projector therefore has a nonzero rank-two image with an injective restriction of the literal root-valued Weil pairing. Action comparison, generator, character-compatibility, image-dimension and restricted-nondegeneracy assumptions are all discharged by actual upstream objects.'
boundary='Comparison of this image with the existing spanning primitive specialization, the separate primitive Frobenius determinant, residual association, arithmetic automorphy and all-weight continuation remain required. The Frobenius quadratic identity alone does not prove the determinant. 16/20; DUB-17--20 OPEN.'
route='Reuse native finite-source Hom base change and flat tensor injection, with no finiteness assumption on the root-valued target. Reuse the original cusp/lattice Hecke relations, all-word rank-two Tate coordinates, prescribed p-adic eigencharacter, algebraIdempotentLeftIdeal and native range/finite-product equivalences. Only good-prime adjointness enters the projector. The same arithmetic projector supplies both rank two and restricted Weil nondegeneracy. Next reuse native range_liftBaseChange to compare with the existing spanning specialization; retain the original representation. No second determinant descent, new eigencharacter, generic Jacobian representability, external import, root pin change or proof-limit change is introduced.'
status='The actual nondegenerate rank-two primitive Tate image passes 140 exhaustive scratch checks and 66 explicit axiom queries across 31 modules, with sixteen linters per module and zero diagnostics. Three declaration-value audits verify 91 required dependencies. Three additional public coordinate identities are separately axiom-checked as reflexivity proofs; no erased named dependency is claimed. Production aggregate, focused audit and sequential foundation/paper verification of the 8,133-module scope are pending.'
routePath=p/'original-primitive-tate-image-promotion-route-563.json';assert not routePath.exists()
routePath.write_text(json.dumps(dict(scope=563,scopeIds=[560,561,562],receipts=digests,dependency=dependency,discharged=discharged,remaining=boundary,route=route,precedingCanonicalScope=8102,mathematicalSource='Frozen Dubon arXiv2609.17875v1; complete original goal unchanged.',rootPinsChanged=False,proofLimitsChanged=False,externalLocalBuild=False,externalImport=False),indent=2)+'\n',encoding='utf-8')
def transform(s):
 s=s.replace('OriginalPrimitiveProjector','OriginalPrimitiveTateImage').replace('original_primitive_projector','original_primitive_tate_image').replace('primitive-projector','primitive-tate-image').replace('PRIMITIVE PROJECTOR','PRIMITIVE TATE IMAGE')
 s=s.replace('OriginalWeilNondegeneracy','OriginalPrimitiveProjector')
 s=s.replace('8102','8133').replace('8075','8102').replace('8,102','8,133').replace('8,075','8,102')
 s=s.replace('promotion-route-559','promotion-route-563').replace('20261025-559','20261025-563')
 return s
def output(name,s):
 f=p/name;assert not f.exists();f.write_text(s,encoding='utf-8')
s=transform((p/'integrate_source_original_primitive_projector_8102.py').read_text(encoding='utf-8'))
s=re.sub(r'^digests = .+$',lambda _:'digests = '+repr(digests),s,flags=re.M)
s=s.replace('(27, 27, 61, 51, 10)','(31, 31, 66, 53, 13)').replace('count == 89','count == 140')
for label,value in [('dependency',dependency),('discharged',discharged),('boundary',boundary),('status',status),('route',route)]:
 s=re.sub(r'^'+label+r' = .+$',lambda _,label=label,value=value:label+' = '+repr(value),s,flags=re.M)
s=s.replace('Actual rational Weil pairing and arithmetic primitive projector (','Actual nondegenerate rank-two primitive Tate image (')
a=s.index('evidence += [p/name for name in digests]');b=s.index("for cert in certs:\n    for field in ['log','dependencyAuditLog']:",a)
extra=['prepare_primitive_tate_restriction_audit_561.py','prepare_primitive_tate_restriction_audit_561b.py','prepare_primitive_rank_two_audit_562.py','prepare_primitive_rank_two_dependency_successor_562b.py','primitive-rank-two-route-562.json','source-original-primitive-rank-two-17-audit-config.json','SourceOriginalPrimitiveRankTwoDependencyAudit17.lean','SourceOriginalPrimitiveRankTwoDependencyAudit17.log','SourceOriginalPrimitiveRankTwoDependencyAudit17.exit','record_coefficient_weil_560.py','record_primitive_tate_restriction_561.py','record_primitive_rank_two_562.py']
configs=[stems[0]+'-audit-config.json',stems[1]+'-audit-config.json',stems[2]+'-audit-config-562b.json']
s=s[:a]+"evidence += [p/name for name in digests]\nevidence += [p/name for name in "+repr(routes+extra+configs)+"]\nfor cert in certs:\n    evidence.append(Path(cert['reuseReview']))\n\n"+s[b:]
oldEdge='  PRIMITIVEPROJECTOR8102["Actual rational Weil nondegeneracy and nonzero arithmetic primitive idempotent; original Tate realization, component restriction and determinant OPEN (DUB-17/18)"] --> CMARITH4538'
newEdge='  PRIMITIVEPROJECTOR8102["Actual rational Weil nondegeneracy and nonzero arithmetic primitive idempotent (DUB-17/18)"] --> PRIMITIVETATEIMAGE8133\n  PRIMITIVETATEIMAGE8133["Actual nondegenerate rank-two primitive Tate image; spanning-specialization comparison and determinant OPEN (DUB-17/18)"] --> CMARITH4538'
s=re.sub(r'^edge = .+$',lambda _:'edge = '+repr(oldEdge),s,flags=re.M)
s=re.sub(r'^arch.write_text\(.*$',lambda _:"arch.write_text(arch.read_text(encoding='utf-8').replace(edge, "+repr(newEdge)+"),encoding='utf-8')",s,flags=re.M)
s=s.replace('Actual rational Weil pairing and arithmetic primitive projector - ','Actual nondegenerate rank-two primitive Tate image - ')
s=s.replace('Actual rational Weil nondegeneracy and a nonzero arithmetic primitive idempotent are proved. Original Tate realization, required component restriction, determinant, residual association, automorphy and all-weight continuation remain open; 16/20 gates.','The actual arithmetic projector has a nonzero rank-two original Tate image with an injective restricted Weil pairing. Comparison to the existing spanning specialization, determinant, residual association, automorphy and all-weight continuation remain open; 16/20 gates.')
s=s.replace('"increment": 27, "queries": 61','"increment": 31, "queries": 66')
compile(s,'integrator8133','exec');output('integrate_source_original_primitive_tate_image_8133.py',s)
for stem in ['prepare_original_primitive_projector_production_ownership','prepare_original_primitive_projector_scratch_ownership','compare_original_primitive_projector_ownership','record_source_original_primitive_projector','verify_original_primitive_projector']:
 ext='.ps1' if stem.startswith('verify') else '.py'
 s=transform((p/(stem+'_8102'+ext)).read_text(encoding='utf-8'))
 if stem.startswith('compare'):s=s.replace('==4','==3').replace('==89','==140')
 if stem.startswith('record'):
  s=re.sub(r'\b89\b','140',s);s=re.sub(r'\b27\b','31',s)
  s=s.replace('== 4','== 3').replace('== 2199','== 2212').replace('== 23539','== 23592')
  s=s.replace('actual rational Weil pairing and arithmetic primitive projector','actual nondegenerate rank-two primitive Tate image').replace('Four declaration-value audits verify 84 required dependencies.','Three declaration-value audits verify 91 required dependencies.')
 if ext=='.py':compile(s,stem+'8133','exec')
 output(stem.replace('primitive_projector','primitive_tate_image')+'_8133'+ext,s)
print(json.dumps(dict(modules=31,queries=66,theorems=53,constructions=13,scratchChecks=140,proofEdges=91,receipts=digests,routeSha256=sha(routePath))))
