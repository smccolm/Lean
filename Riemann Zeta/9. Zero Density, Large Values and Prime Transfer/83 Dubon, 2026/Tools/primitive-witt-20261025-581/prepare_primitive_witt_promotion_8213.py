from pathlib import Path
import re,json,hashlib
p=Path(__file__).parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
stems=['source-primitive-residual-determinant-3','source-primitive-residual-oddness-2','source-primitive-finite-residual-4','source-primitive-witt-framed-4','source-primitive-witt-fixed-7']
paths=[p/(s+'-scratch-receipt.json') for s in stems]
certs=[json.loads(f.read_text(encoding='utf-8')) for f in paths]
mods=[m for c in certs for m in c['modules']]
queries=[q for c in certs for q in c['queries']]
ths=[q for c in certs for q in c['theoremRegistrations']]
defs=[q for c in certs for q in c['constructionRegistrations']]
assert (len(mods),len(set(mods)),len(queries),len(ths),len(defs))==(20,20,36,29,7)
count=sum(c['exhaustiveTheorems'] for c in certs)
edges=sum(c['requiredProofValueEdges'] for c in certs)
digests={f.name:sha(f) for f in paths}
dependency='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> actual original all-weight residual deformation problem -> global cyclotomic determinant, real oddness, finite coefficients and genuine p-adic fixed-determinant quotient'
discharged='The original primitive form in every weight at least two and every prescribed prime supplies the same original-support residual representation over a constructed finite field. Its global determinant is the cyclotomic power k-1; its determinant at actual complex conjugation is minus one. Original Fourier reductions, good-prime determinants and inertia remain unchanged. The native Witt coefficient ring has precisely this finite residue field. The existing actual framed and fixed-determinant rings are Noetherian and complete and their universal matrices reduce to that same representation. Every p-power root lies in the original arithmetic extension by support-power inclusion, so the native p-adic cyclotomic character has the actual root action. Its Witt scalar image reduces to the original finite character and supplies the genuine weight determinant of the fixed-determinant quotient. No global residual determinant, oddness, finite coefficient, Witt residue, prime-power root or determinant compatibility assumption remains.'
boundary='A characteristic-zero coefficient ring does not provide a characteristic-zero point of the deformation ring. Original all-weight adic association, required local, image and regularity properties, arithmetic automorphy and literal higher symmetric-power continuation remain required. 16/20; DUB-17--20 OPEN.'
route='Reuse the proved original residual association and character density, native finite algebraic adjunction and coefficient mapping, SourceWittLift and native Witt DVR/completeness, and the existing actual framed and fixed-determinant constructions. Native WittVector.fromPadicInt and cyclotomicCharacter avoid new scalar-lift and character infrastructure; existing support-power inclusion supplies all required roots. The renewed primary-source review finds overlapping weight-two code and a later Hodge-Tate candidate, without a ready all-weight association proof. No external import, root pin, proof-limit change or incidental generalization.'
status=f'The actual original-form residual determinant and deformation chain passes {count} exhaustive scratch checks and 36 explicit axiom queries across 20 modules, with sixteen linters per module and zero diagnostics. Five declaration-value audits verify {edges} required dependencies. Failed serialization checks and fresh successors, plus stopped unaudited elaboration attempts and unchanged-conclusion refinements, are preserved. Production aggregate, focused audit and sequential foundation/paper verification of the 8,213-module scope are pending.'
rp=p/'primitive-witt-deformation-promotion-route-581.json'
assert not rp.exists()
rp.write_text(json.dumps(dict(scope=581,scopeIds=[572,574,575,577,580],receipts=digests,dependency=dependency,discharged=discharged,remaining=boundary,route=route,precedingCanonicalScope=8193,mathematicalSource='Frozen Dubon arXiv2609.17875v1; complete original goal unchanged.',rootPinsChanged=False,proofLimitsChanged=False,externalLocalBuild=False,externalImport=False),indent=2)+'\n',encoding='utf-8')
def transform(s):
 for a,b in [('PrimitiveResidualAssociation','PrimitiveWittDeformation'),('primitive_residual_association','primitive_witt_deformation'),('source-primitive-residual-association','source-primitive-witt-deformation'),('primitive-residual-association-promotion','primitive-witt-deformation-promotion'),('primitive-residual-20261025-573','primitive-witt-20261025-581'),('PRIMITIVE RESIDUAL ASSOCIATION','PRIMITIVE WITT DEFORMATION'),('OriginalPrimitiveFrobenius','PrimitiveResidualAssociation'),('original_primitive_frobenius','primitive_residual_association'),('source-original-primitive-frobenius','source-primitive-residual-association'),('primitive-frobenius-20261025-569','primitive-residual-20261025-573'),('8193','8213'),('8159','8193'),('8,193','8,213'),('8,159','8,193'),('promotion-route-573','promotion-route-581')]:s=s.replace(a,b)
 return s
def output(name,s):
 f=p/name;assert not f.exists(),f
 if f.suffix=='.py':compile(s,str(f),'exec')
 f.write_text(s,encoding='utf-8')
s=transform((p/'integrate_source_primitive_residual_association_8193.py').read_text(encoding='utf-8'))
s=re.sub(r'^digests = .+$',lambda _:'digests = '+repr(digests),s,flags=re.M)
s=s.replace('(34, 34, 58, 52, 6)','(20, 20, 36, 29, 7)').replace('count == 137',f'count == {count}')
for label,value in [('dependency',dependency),('discharged',discharged),('boundary',boundary),('status',status),('route',route)]:
 s=re.sub(r'^'+label+r' = .+$',lambda _,label=label,value=value:label+' = '+repr(value),s,flags=re.M)
s=s.replace('Actual all-weight original-support residual association (','Actual original-form cyclotomic determinant and deformation rings (')
s=s.replace('Actual all-weight original-support residual association - ','Actual original-form cyclotomic determinant and deformation rings - ')
a=s.index('evidence += [p/name for name in digests]');b=s.index("for cert in certs:\n    for field in ['log','dependencyAuditLog']:",a)
extra=[]
for f in p.iterdir():
 if not f.is_file() or f.suffix not in ['.py','.ps1','.json','.lean','.log','.exit']:continue
 if re.search(r'(572|574|575|577|580)(?:[a-z])?\.',f.name) or f.name.startswith(('SourcePrimitiveResidualDeterminantAudit','SourcePrimitiveResidualDeterminantDependencyAudit','SourcePrimitiveResidualOddnessAudit','SourcePrimitiveResidualOddnessDependencyAudit','SourcePrimitiveFiniteResidualAudit','SourcePrimitiveFiniteResidualDependencyAudit','SourcePrimitiveWittFramedAudit','SourcePrimitiveWittFramedDependencyAudit','SourcePrimitiveWittFixedAudit','SourcePrimitiveWittFixedDependencyAudit')):
  extra.append(f.name)
extra+= [stem+'-audit-config.json' for stem in stems]
for name in extra:assert (p/name).exists(),name
s=s[:a]+"evidence += [p/name for name in digests]\nevidence += [p/name for name in "+repr(sorted(set(extra)))+"]\nfor folder in ['finite-residual-575-before-abstract-descent','witt-framed-577-before-named-conclusion']:\n    evidence += sorted((p/folder).iterdir())\nfor cert in certs:\n    evidence.append(Path(cert['reuseReview']))\n\n"+s[b:]
old="target=r/archive_rel/('prescribed-completion-568-pre-doc-audit' if source.parent.name=='prescribed-completion-568-pre-doc-audit' else '')/(source.name+('.txt' if source.suffix=='.lean' else ''))"
assert old in s
s=s.replace(old,"target=r/archive_rel/(source.parent.name if source.parent != p else '')/(source.name+('.txt' if source.suffix=='.lean' else ''))")
edge='  PRIMITIVERESIDUAL8193["All-weight original-support residual association: coefficient completion, norm-local comparison, arithmetic descent and parabolic closure proved; global determinant, adic realization, local/image properties and automorphy OPEN (DUB-17/18)"] --> CMARITH4538'
newedge='  PRIMITIVERESIDUAL8193["All-weight original-support residual association with original Fourier reductions and inertia (DUB-17/18)"] --> PRIMITIVEWITT8213\n  PRIMITIVEWITT8213["Global cyclotomic determinant, real oddness, finite residue field and actual complete Witt framed/fixed-determinant rings proved; original adic point, local/image/regularity and automorphy OPEN (DUB-17/18)"] --> CMARITH4538'
s=re.sub(r'^edge = .+$',lambda _:'edge = '+repr(edge),s,flags=re.M)
s=re.sub(r'^arch.write_text\(.*$',lambda _:"arch.write_text(arch.read_text(encoding='utf-8').replace(edge, "+repr(newedge)+"),encoding='utf-8')",s,flags=re.M)
s=s.replace('"increment": 34, "queries": 58','"increment": 20, "queries": 36')
oldsum='The actual original primitive form in every weight at least two supplies its prescribed-characteristic residual representation on the original support, with exact original coefficient reduction, weight determinant and good-prime inertia. Global determinant, adic realization, local/image properties, automorphy and all-weight continuation remain open; 16/20 gates.'
s=s.replace(oldsum,'The original all-weight form supplies its finite-field residual representation with global cyclotomic determinant and real oddness, together with actual complete framed and genuine cyclotomic fixed-determinant rings over Witt coefficients. Original adic specialization, local/image/regularity properties, automorphy and literal higher continuation remain open; 16/20 gates.')
output('integrate_source_primitive_witt_deformation_8213.py',s)
for stem in ['prepare_primitive_residual_association_production_ownership','prepare_primitive_residual_association_scratch_ownership','compare_primitive_residual_association_ownership','record_source_primitive_residual_association','prepare_primitive_residual_association_global_ownership']:
 suffix='b' if stem.startswith('compare') else ''
 s=transform((p/(stem+'_8193'+suffix+'.py')).read_text(encoding='utf-8'))
 if stem.startswith('compare'):s=re.sub(r'==3\b','==5',s).replace('==137',f'=={count}')
 if stem.startswith('record'):
  s=re.sub(r'\b137\b',str(count),s);s=re.sub(r'\b34\b','20',s)
  s=re.sub(r'== 3\b','== 5',s).replace('== 2220','== 2227').replace('== 23692','== 23721')
  s=s.replace('actual all-weight original-support residual association','actual original-form cyclotomic determinant and deformation rings')
  s=s.replace('Three declaration-value audits verify 103 required dependencies.',f'Five declaration-value audits verify {edges} required dependencies.')
 output(stem.replace('primitive_residual_association','primitive_witt_deformation')+'_8213.py',s)
s=transform((p/'verify_primitive_residual_association_8193c.ps1').read_text())
s=s.replace('compare_primitive_witt_deformation_ownership_8213b.py','compare_primitive_witt_deformation_ownership_8213.py')
output('verify_primitive_witt_deformation_8213.ps1',s)
print(json.dumps(dict(modules=20,queries=36,theorems=29,constructions=7,scratchChecks=count,proofEdges=edges,receipts=digests,routeSha256=sha(rp))))
