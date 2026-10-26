from pathlib import Path
import re,json,hashlib
p=Path(__file__).parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
stems=['source-binary-prime-power-permutation-5','source-primitive-h1-adic-5','source-binary-stabilizer-h1-3','source-primitive-h1-congruence-5','source-primitive-finite-operator-character-4']
paths=[p/(s+'-scratch-receipt.json') for s in stems]
certs=[json.loads(f.read_text(encoding='utf-8')) for f in paths]
mods=[m for c in certs for m in c['modules']]
queries=[n for c in certs for n in c['queries']]
ths=[n for c in certs for n in c['theoremRegistrations']]
defs=[n for c in certs for n in c['constructionRegistrations']]
assert (len(mods),len(set(mods)),len(queries),len(ths),len(defs))==(22,22,56,39,17)
count=sum(c['exhaustiveTheorems'] for c in certs)
edges=sum(c['requiredProofValueEdges'] for c in certs)
assert (count,edges)==(126,93)
digests={f.name:sha(f) for f in paths}
dependency='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero Galois association -> compatible geometric finite-precision Hecke realizations -> actual finite operator characters, original coefficient congruences and finite congruence-stabilizer H1 comparison'
discharged='For every original primitive form of weight at least two and every prescribed prime, the same original integral H1 Hecke character is valued in its literal Fourier coefficient field and actual local valuation ring. Its finite adic reductions are compatible as whole characters and have the exact original Fourier values. The nonzero faithful character fiber and native finite-lattice integrality prove that original operator congruences force matching character congruences. Every character therefore factors through the actual finite tensor-reduced H1 operator ring, with exact original pullback and prime values. Independently, at every positive power of every prime greater than three, the actual finite binary permutation coefficients map onto original H1 and retain all original prime Hecke transforms. Existing orbit, finite-product and Shapiro maps identify these permutation H1 groups with trivial-coefficient H1 of their actual finite-index congruence stabilizers. All coefficient-field, integrality, finite-residue, adic compatibility, character-kernel and cohomological comparison inputs in these consumers are derived.'
boundary='The transported stabilizer operators have not yet been identified with arithmetic geometric correspondences. Geometric Galois realization of these finite characters, compatible characteristic-zero association, required local/image/regularity properties, arithmetic automorphy and literal higher symmetric-power continuation remain required. No eigenvector lift, arithmetic Galois action or characteristic-zero deformation point is claimed from the finite constructions alone. 16/20; DUB-17--20 OPEN.'
route='Reuse the existing integral H1 character, finite Hecke algebra, Fourier field and prescribed-prime completion; native quotient powers, finite-lattice integrality and tensor base change; the existing exact semilinear reduction kernel, faithful character fiber, finite permutation evaluation, Gamma0 H1 surjection, full Hecke naturality, orbit decomposition and Shapiro comparison. Explicit descent arguments avoid elaboration timeouts without changing hypotheses or proof limits. Native finite-index counit and new H2 torsion infrastructure are deferred because they are unnecessary for this route. The renewed primary-source search remains recorded; no external import or root pin change.'
status=f'The actual original-form finite H1 realization chain passes {count} exhaustive scratch checks and 56 explicit axiom queries across 22 modules, with sixteen linters per module and zero diagnostics. Five declaration-value audits verify {edges} required dependencies. The superseded dependency expectation and both timed-out unaudited elaboration attempts are preserved with their exact successors. Production aggregate, focused audit and sequential foundation/paper verification of the 8,235-module scope are pending.'
rp=p/'primitive-finite-h1-promotion-route-587.json'
assert not rp.exists()
rp.write_text(json.dumps(dict(scope=587,scopeIds=[582,583,584,585,586],receipts=digests,dependency=dependency,discharged=discharged,remaining=boundary,route=route,precedingCanonicalScope=8213,mathematicalSource='Frozen Dubon arXiv2609.17875v1; complete original goal unchanged.',rootPinsChanged=False,proofLimitsChanged=False,externalImport=False),indent=2)+'\n',encoding='utf-8')
replacements={
'primitive-witt-deformation-promotion-route-581.json':'primitive-finite-h1-promotion-route-587.json',
'Tools/primitive-witt-20261025-581':'Tools/primitive-finite-h1-20261025-587',
'Tools/primitive-residual-20261025-573':'Tools/primitive-witt-20261025-581',
'appliedSourcePrimitiveWittDeformation':'appliedSourcePrimitiveFiniteH1Realization',
'appliedSourcePrimitiveResidualAssociation':'appliedSourcePrimitiveWittDeformation',
'SourcePrimitiveWittDeformation':'SourcePrimitiveFiniteH1Realization',
'SourcePrimitiveResidualAssociation':'SourcePrimitiveWittDeformation',
'SOURCE PRIMITIVE WITT DEFORMATION':'SOURCE PRIMITIVE FINITE H1 REALIZATION',
'primitive_witt_deformation':'primitive_finite_h1_realization',
'primitive_residual_association':'primitive_witt_deformation',
'primitive-witt-deformation':'primitive-finite-h1-realization',
'primitive-residual-association':'primitive-witt-deformation',
'8,213':'8,235','8,193':'8,213','8213':'8235','8193':'8213'}
pattern=re.compile('|'.join(re.escape(k) for k in sorted(replacements,key=len,reverse=True)))
transform=lambda s:pattern.sub(lambda m:replacements[m[0]],s)
def output(name,s):
 f=p/name;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
s=transform((p/'integrate_source_primitive_witt_deformation_8213.py').read_text(encoding='utf-8'))
s=re.sub(r'^digests = .+$',lambda _: 'digests = '+repr(digests),s,flags=re.M)
s=s.replace('(20, 20, 36, 29, 7)','(22, 22, 56, 39, 17)').replace('count == 62','count == 126')
for label,value in [('dependency',dependency),('discharged',discharged),('boundary',boundary),('status',status),('route',route)]:
 s=re.sub(r'^'+label+r' = .+$',lambda _,label=label,value=value:label+' = '+repr(value),s,flags=re.M)
s=s.replace('Actual original-form cyclotomic determinant and deformation rings (','Actual original finite H1 characters and congruence realizations (').replace('Actual original-form cyclotomic determinant and deformation rings - ','Actual original finite H1 characters and congruence realizations - ')
a=s.index('evidence += [p/name for name in digests]');b=s.index("for cert in certs:\n    for field in ['log','dependencyAuditLog']:",a)
prefixes=['SourceBinaryPrimePowerPermutationAudit','SourceBinaryPrimePowerPermutationDependencyAudit','SourcePrimitiveH1AdicAudit','SourcePrimitiveH1AdicDependencyAudit','SourceBinaryStabilizerH1Audit','SourceBinaryStabilizerH1DependencyAudit','SourcePrimitiveH1CongruenceAudit','SourcePrimitiveH1CongruenceDependencyAudit','SourcePrimitiveFiniteOperatorCharacterAudit','SourcePrimitiveFiniteOperatorCharacterDependencyAudit']
extra=[]
for f in p.iterdir():
 if not f.is_file() or f.suffix not in ['.py','.ps1','.json','.lean','.log','.exit']:continue
 if re.search(r'(?<!\d)(582|583|584|585|586)[a-z]?\.',f.name) or f.name.startswith(tuple(prefixes)):
  extra.append(f.name)
extra += [s+'-audit-config.json' for s in stems]
for name in extra:assert (p/name).exists(),name
s=s[:a]+"evidence += [p/name for name in digests]\nevidence += [p/name for name in "+repr(sorted(set(extra)))+"]\nfor folder in ['finite-operator-586-before-abstract-descent','finite-operator-586-before-explicit-descent-arguments']:\n    evidence += sorted((p/folder).iterdir())\nfor cert in certs:\n    evidence.append(Path(cert['reuseReview']))\n\n"+s[b:]
edge='  PRIMITIVEWITT8213["Global cyclotomic determinant, real oddness, finite residue field and actual complete Witt framed/fixed-determinant rings proved; original adic point, local/image/regularity and automorphy OPEN (DUB-17/18)"] --> CMARITH4538'
newedge='  PRIMITIVEWITT8213["Global cyclotomic determinant, real oddness, finite residue field and actual complete Witt framed/fixed-determinant rings (DUB-17/18)"] --> PRIMITIVEFINITEH18235\n  PRIMITIVEFINITEH18235["Compatible original finite H1 operator characters and congruence-stabilizer comparison proved; geometric Galois realization, adic association, local/image/regularity and automorphy OPEN (DUB-17/18)"] --> CMARITH4538'
s=re.sub(r'^edge = .+$',lambda _:'edge = '+repr(edge),s,flags=re.M)
s=re.sub(r'^arch.write_text\(.*$',lambda _:"arch.write_text(arch.read_text(encoding='utf-8').replace(edge, "+repr(newedge)+"),encoding='utf-8')",s,flags=re.M)
s=s.replace('"increment": 20, "queries": 36','"increment": 22, "queries": 56')
s=s.replace('The original all-weight form supplies its finite-field residual representation with global cyclotomic determinant and real oddness, together with actual complete framed and genuine cyclotomic fixed-determinant rings over Witt coefficients. Original adic specialization, local/image/regularity properties, automorphy and literal higher continuation remain open; 16/20 gates.','The original all-weight form supplies compatible finite adic H1 characters on the actual finite operator image, with original Fourier values and operator-congruence compatibility. Original finite permutation H1 is identified with actual congruence-stabilizer H1 while retaining Hecke transforms. Geometric Galois realization, adic association, local/image/regularity, automorphy and higher continuation remain open; 16/20 gates.')
s=s.replace('The original primitive cusp form, Fourier coefficients, actual local fields, arithmetic support, parabolic cohomology and weight twist retain their definitions.','The original primitive cusp form, Fourier coefficients, actual local fields, integral H1, Hecke operators, coefficient reductions and original finite permutation and stabilizer cohomology retain their definitions.')
output('integrate_source_primitive_finite_h1_realization_8235.py',s)
for stem in ['prepare_primitive_witt_deformation_production_ownership','prepare_primitive_witt_deformation_scratch_ownership','compare_primitive_witt_deformation_ownership','record_source_primitive_witt_deformation','prepare_primitive_witt_deformation_global_ownership']:
 s=transform((p/(stem+'_8213.py')).read_text(encoding='utf-8'))
 s=re.sub(r'\b62\b','126',s)
 if stem.startswith('compare'):s=s.replace('All 20 mathematical source bodies','All 22 mathematical source bodies')
 if stem.startswith('record'):
  s=re.sub(r'\b20\b','22',s).replace('== 2227','== 2244').replace('== 23721','== 23760')
  s=s.replace('actual original-form cyclotomic determinant and deformation rings','actual original finite H1 characters and congruence realizations')
  s=s.replace('Five declaration-value audits verify 63 required dependencies.','Five declaration-value audits verify 93 required dependencies.')
 output(stem.replace('primitive_witt_deformation','primitive_finite_h1_realization')+'_8235.py',s)
for stem in ['build_primitive_witt_deformation','verify_primitive_witt_deformation']:
 output(stem.replace('primitive_witt_deformation','primitive_finite_h1_realization')+'_8235.ps1',transform((p/(stem+'_8213.ps1')).read_text(encoding='utf-8')))
s=transform((p/'archive_primitive_witt_canonical_8213.py').read_text(encoding='utf-8')).replace('archive_primitive_witt_canonical_','archive_primitive_finite_h1_canonical_')
output('archive_primitive_finite_h1_canonical_8235.py',s)
print(json.dumps(dict(modules=22,queries=56,theorems=39,constructions=17,scratchChecks=count,proofEdges=edges,routeSha256=sha(rp),evidenceFiles=len(set(extra)),productionMutation=False)))
