from pathlib import Path
import re,json,hashlib
p=Path(__file__).parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
stems=['source-original-prescribed-completion-11','source-original-arithmetic-residual-11','source-primitive-residual-galois-12']
certPaths=[p/(s+'-scratch-receipt.json') for s in stems]
certs=[json.loads(f.read_text(encoding='utf-8')) for f in certPaths]
mods=[m for c in certs for m in c['modules']]; queries=[n for c in certs for n in c['queries']]
ths=[n for c in certs for n in c['theoremRegistrations']]; defs=[n for c in certs for n in c['constructionRegistrations']]
assert (len(mods),len(set(mods)),len(queries),len(ths),len(defs))==(34,34,58,52,6)
assert sum(c['exhaustiveTheorems'] for c in certs)==137
assert sum(c['requiredProofValueEdges'] for c in certs)==103
digests={f.name:sha(f) for f in certPaths}
routes=['prescribed-completion-route-568b.json','arithmetic-residual-route-570.json','primitive-residual-galois-route-571b.json']
dependency='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> actual all-weight primitive Galois association -> close the residual association branch at the original arithmetic support Qp, with the original Fourier coefficients, weight determinant and good-prime inertia'
discharged='For every original primitive form of weight at least two and every prescribed rational prime, construct the actual finite local coefficient field, residue closure of that characteristic and continuous residual representation on the original arithmetic group of support Qp. Its good-prime Frobenius trace is the reduction of the original Fourier coefficient, its determinant is q^(k-1), and its good-prime inertia is trivial. The prescribed algebraic-integer reduction selects the coefficient completion and residue map. Actual norm-local Frobenius and inertia are compared with the source valuation, and the representation descends through the arithmetic quotient. The parabolic alternative is eliminated by actual Petersson-adjoint level descent and normalization to a primitive divisor; the existing weight twist and support equality restore the original weight and level. None of these steps remains an additional representation, coefficient-field, local-compatibility or parabolic-realization hypothesis.'
boundary='The global residual determinant identity, all-weight adic realization and required local, regularity and image properties, arithmetic automorphy and literal higher symmetric-power continuation remain required. This closes residual association, not the full Galois or analytic endpoint. 16/20; DUB-17--20 OPEN.'
route='Reuse the native completion and residue equivalences, finite Galois factors and original arithmetic support embeddings; reuse the proved Petersson inner product, commuting Hecke eigenvectors, newform normalization, residual weight-two reduction, cyclotomic twist and support comparison. The same original coefficients and exact source local actions are retained. No external import, root pin change, proof-limit change or incidental generalization is used.'
status='The all-weight original-support residual association passes 137 exhaustive scratch checks and 58 explicit axiom queries across 34 modules, with sixteen linters per module and zero diagnostics. Three declaration-value audits verify 103 required dependencies. The failed documentation audit and its unchanged-mathematics successor, and the route-serialization failure and corrected successor, are preserved. Production aggregate, focused audit and sequential foundation/paper verification of the 8,193-module scope are pending.'
routePath=p/'primitive-residual-association-promotion-route-573.json'; assert not routePath.exists()
routePath.write_text(json.dumps(dict(scope=573,scopeIds=[568,570,571],receipts=digests,dependency=dependency,discharged=discharged,remaining=boundary,route=route,precedingCanonicalScope=8159,mathematicalSource='Frozen Dubon arXiv2609.17875v1; complete original goal unchanged.',rootPinsChanged=False,proofLimitsChanged=False,externalLocalBuild=False,externalImport=False),indent=2)+'\n',encoding='utf-8')
def transform(s):
 s=s.replace('OriginalPrimitiveFrobenius','PrimitiveResidualAssociation').replace('original_primitive_frobenius','primitive_residual_association').replace('source-original-primitive-frobenius','source-primitive-residual-association').replace('original-primitive-frobenius-promotion','primitive-residual-association-promotion').replace('primitive-frobenius-20261025-569','primitive-residual-20261025-573').replace('ORIGINAL PRIMITIVE FROBENIUS','PRIMITIVE RESIDUAL ASSOCIATION')
 s=s.replace('OriginalPrimitiveTateImage','OriginalPrimitiveFrobenius')
 s=s.replace('8159','8193').replace('8133','8159').replace('8,159','8,193').replace('8,133','8,159')
 s=s.replace('promotion-route-569','promotion-route-573')
 s=s.replace('primitive-tate-image-20261025-563','primitive-frobenius-20261025-569')
 return s
def output(name,s):
 f=p/name;assert not f.exists();f.write_text(s,encoding='utf-8')
s=transform((p/'integrate_source_original_primitive_frobenius_8159.py').read_text(encoding='utf-8'))
s=re.sub(r'^digests = .+$',lambda _:'digests = '+repr(digests),s,flags=re.M)
s=s.replace('(26, 26, 50, 48, 2)','(34, 34, 58, 52, 6)').replace('count == 74','count == 137')
for label,value in [('dependency',dependency),('discharged',discharged),('boundary',boundary),('status',status),('route',route)]:
 s=re.sub(r'^'+label+r' = .+$',lambda _,label=label,value=value:label+' = '+repr(value),s,flags=re.M)
s=s.replace('Actual primitive Frobenius and prescribed residual realization (','Actual all-weight original-support residual association (')
a=s.index('evidence += [p/name for name in digests]');b=s.index("for cert in certs:\n    for field in ['log','dependencyAuditLog']:",a)
extra=['prepare_prescribed_completion_audit_568.py','prepare_prescribed_completion_audit_568b.py','repair_prescribed_completion_documentation_568b.py','record_prescribed_completion_568.py','prescribed-completion-route-568.json','prescribed-completion-documentation-successor-568b.json','SourceOriginalPrescribedCompletionAudit11.lean','SourceOriginalPrescribedCompletionAudit11.log','SourceOriginalPrescribedCompletionAudit11.exit','SourceOriginalPrescribedCompletionDependencyAudit11.lean','prepare_arithmetic_residual_audit_570.py','record_arithmetic_residual_570.py','prepare_primitive_residual_galois_audit_571.py','record_primitive_residual_galois_571.py','record_primitive_residual_galois_571b.py','primitive-residual-galois-route-571.json','primitive-residual-galois-route-successor-571b.json']
configs=['source-original-prescribed-completion-11-audit-config.json','source-original-prescribed-completion-11-audit-config-568b.json','source-original-arithmetic-residual-11-audit-config.json','source-primitive-residual-galois-12-audit-config.json']
for name in routes+extra+configs: assert (p/name).exists(),name
s=s[:a]+"evidence += [p/name for name in digests]\nevidence += [p/name for name in "+repr(routes+extra+configs)+"]\nevidence += sorted((p/'prescribed-completion-568-pre-doc-audit').iterdir())\nfor cert in certs:\n    evidence.append(Path(cert['reuseReview']))\n\n"+s[b:]
s=s.replace("target=r/archive_rel/(source.name+('.txt' if source.suffix=='.lean' else ''))","target=r/archive_rel/('prescribed-completion-568-pre-doc-audit' if source.parent.name=='prescribed-completion-568-pre-doc-audit' else '')/(source.name+('.txt' if source.suffix=='.lean' else ''))")
oldEdge='  PRIMITIVEFROBENIUS8159["Same original primitive representation: cyclotomic determinant, exact Frobenius polynomial and prescribed-embedding residual realization; source reduction, arithmetic quotient and norm-local comparisons OPEN (DUB-17/18)"] --> CMARITH4538'
newEdge='  PRIMITIVEFROBENIUS8159["Same original primitive representation: cyclotomic determinant, exact Frobenius polynomial and prescribed-embedding residual realization (DUB-17/18)"] --> PRIMITIVERESIDUAL8193\n  PRIMITIVERESIDUAL8193["All-weight original-support residual association: coefficient completion, norm-local comparison, arithmetic descent and parabolic closure proved; global determinant, adic realization, local/image properties and automorphy OPEN (DUB-17/18)"] --> CMARITH4538'
s=re.sub(r'^edge = .+$',lambda _:'edge = '+repr(oldEdge),s,flags=re.M)
s=re.sub(r'^arch.write_text\(.*$',lambda _:"arch.write_text(arch.read_text(encoding='utf-8').replace(edge, "+repr(newEdge)+"),encoding='utf-8')",s,flags=re.M)
s=s.replace('Actual primitive Frobenius and prescribed residual realization - ','Actual all-weight original-support residual association - ')
s=s.replace('The same original primitive representation has cyclotomic determinant, exact Frobenius trace/determinant/characteristic polynomial, and a prescribed-embedding residual realization. Source reduction compatibility, arithmetic quotient and norm-local comparisons, automorphy and all-weight continuation remain open; 16/20 gates.','The actual original primitive form in every weight at least two supplies its prescribed-characteristic residual representation on the original support, with exact original coefficient reduction, weight determinant and good-prime inertia. Global determinant, adic realization, local/image properties, automorphy and all-weight continuation remain open; 16/20 gates.')
s=s.replace('"increment": 26, "queries": 50','"increment": 34, "queries": 58')
s=s.replace('The original rational Tate module and root-valued Weil pairing, actual cusp forms, integral Hecke algebra and prescribed primitive coefficient field retain their definitions.','The original primitive cusp form, Fourier coefficients, actual local fields, arithmetic support, parabolic cohomology and weight twist retain their definitions.')
compile(s,'integrator8193','exec'); output('integrate_source_primitive_residual_association_8193.py',s)
for stem in ['prepare_original_primitive_frobenius_production_ownership','prepare_original_primitive_frobenius_scratch_ownership','compare_original_primitive_frobenius_ownership','record_source_original_primitive_frobenius','verify_original_primitive_frobenius','prepare_original_primitive_frobenius_global_ownership']:
 ext='.ps1' if stem.startswith('verify') else '.py'
 s=transform((p/(stem+'_8159'+ext)).read_text(encoding='utf-8'))
 if stem.startswith('compare'): s=s.replace('==4','==3').replace('==74','==137')
 if stem.startswith('record'):
  s=re.sub(r'\b74\b','137',s);s=re.sub(r'\b26\b','34',s)
  s=s.replace('== 4','== 3').replace('== 2214','== 2220').replace('== 23640','== 23692')
  s=s.replace('actual primitive Frobenius and prescribed residual realization','actual all-weight original-support residual association').replace('Four declaration-value audits verify 98 required dependencies.','Three declaration-value audits verify 103 required dependencies.')
 if ext=='.py': compile(s,stem+'8193','exec')
 output(stem.replace('original_primitive_frobenius','primitive_residual_association')+'_8193'+ext,s)
s=(p/'archive_primitive_tate_image_canonical_8133.py').read_text(encoding='utf-8').replace('OriginalPrimitiveTateImage','OriginalPrimitiveFrobenius').replace('primitive_tate_image','primitive_frobenius').replace('primitive-tate-image-20261025-563','primitive-frobenius-20261025-569').replace('8133','8159')
compile(s,'archive8159','exec');output('archive_primitive_frobenius_canonical_8159.py',s)
print(json.dumps(dict(modules=34,queries=58,theorems=52,constructions=6,scratchChecks=137,proofEdges=103,receipts=digests,routeSha256=sha(routePath))))
