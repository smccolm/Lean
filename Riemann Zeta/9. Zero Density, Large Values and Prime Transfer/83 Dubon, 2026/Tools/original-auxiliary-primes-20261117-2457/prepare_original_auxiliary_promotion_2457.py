from pathlib import Path
import ast, hashlib, json

s = Path(__file__).parent
p = Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
digests = {
    'source-original-regular-prime-1-scratch-receipt.json': '334EF60FE3B73F047A5F481753159A204503CB6CCD035A70D9244A3F96A75A48',
    'source-original-detecting-family-2-scratch-receipt.json': 'D6EB8D8B5AB21272E5771AD1308CD4E8073DB28E82D4DF967FE3709B147F10C8',
    'source-original-unramified-dimension-1-scratch-receipt.json': 'E52346CFD7BCEB752F11156364F26F09705DDB99034F137448DFE5810B7A228D',
}
certs = []
for name, digest in digests.items():
    assert sha(s/name) == digest
    certs.append(json.loads((s/name).read_text()))
modules = [m for c in certs for m in c['modules']]
assert len(modules) == len(set(modules)) == 28
assert [sum(len(c[k]) for c in certs) for k in ['queries','theoremRegistrations','constructionRegistrations']] == [40,30,10]
assert [sum(c[k] for c in certs) for k in ['exhaustiveTheorems','exhaustiveOtherDeclarations','requiredProofValueEdges']] == [122,25,412]
archives = [
    ('Tools/original-regular-prime-scratch-20261117-2408/manifest.json','870D73AEAD1E86320582C53CDCF7ACAF45D167DE5262AE2B85DAEFBD9A9E2359'),
    ('Tools/original-detecting-family-scratch-20261117-2430b/manifest.json','521E117D88D7F503F829696B63F1E5CD0998890C8FAA4C4DD07775139963B5EC'),
    ('Tools/original-unramified-dimension-scratch-20261117-2437/manifest.json','C92C0259AC1A366415395CDA10E3B484441E4E47DEF5A5D654F19EF44928ABC8'),
]
for name, digest in archives:
    assert sha(p/name) == digest
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> automorphy -> actual original residual deformation inputs -> regular auxiliary-prime detection, bounded jointly detecting families and original-field unramified adjoint dimension comparison.'
discharged = ('For an actual original primitive cusp form of weight at least two and prime p greater than three, the same constructed residual representation retains all its original integral, reduction, Hecke, Frobenius, determinant and oddness data. In its finite linear subfield branch, every nonzero original symmetric twisted-H1 class with 2*n < p-1 has regular detecting primes outside any finite set and congruent to one modulo every prescribed p-power. The actual common finite affine factor, unramified Frobenius and nonzero original localization are constructed. Every subspace of the original global H1 has a jointly detecting family of cardinality at most its original-field dimension; global H1 finiteness is derived rather than supplied. For every symmetric degree and every rational prime, the original local unramified adjoint H1 dimension equals the actual invariant-space dimension, without a large-image assumption. All prior conclusions concern the same original representation.')
boundary = ('The six small-projective-image alternatives remain explicit and their arithmetic exclusion is still required. The regular-prime invariant dimension is not yet computed in this promoted scope; original local deformation conditions, automorphy and literal higher symmetric-power continuation remain open. The finite subfield is not identified with the original residue field. The actual-form consumer retains weight at least two and p greater than three; full source-domain obligations remain. Acceptance remains 16/20; DUB-17--20 OPEN, with every source and verification criterion unchanged.')
status = ('The 28-module scratch scope passes 40 public axiom queries, all 122 theorem and 25 other declaration checks, sixteen linters per module, exact ownership enumeration and 147 declaration type/value fingerprints. Three source proof-value audits verify 123, 138 and 151 required dependencies, respectively. Production aggregate, focused audits and sequential foundation/paper verification of the 9,783-module scope are pending.')
route = ('Reuse native subfield projectors, perfect SL2 kernels, the original cyclotomic root-fixing argument and genuine conjugate Chebotarev. Original non-coboundary detection avoids a separate H1 scalar-extension comparison. Restricting coefficient scalars injects the same global and local continuous cocycles into already proved finite prime-field cocycle spaces; the original H1 quotient is finite. Native finite_detecting_family_of_pointwise constructs the bounded family. The existing finite-field cyclic-depth theorem proves the original unramified H1/invariant dimension formula. No additional external import, root-pin change, proof-limit change, general cohomology base-change theory or independent image certificate is introduced.')
route_path = s/'original-auxiliary-primes-promotion-route-2457.json'
review = dict(dependency=dependency,discharged=discharged,boundary=boundary,route=route,
    scratchCertificates=[dict(path=n,sha256=h) for n,h in digests.items()],
    immutableScratchArchives=[dict(path=n,sha256=h) for n,h in archives],
    disjointModules=28,publicTheorems=30,publicConstructions=10,
    exhaustiveTheorems=122,exhaustiveOtherDeclarations=25,typeValueFingerprints=147,
    proofValueEdges=[c['requiredProofValueEdges'] for c in certs],
    proofBodiesPreserved=True,changes='Only import qualification during promotion.',accepted=16,total=20)
assert not route_path.exists();route_path.write_text(json.dumps(review,indent=2)+'\n')
report=s/'Dubon Original Auxiliary Primes Assessment 2026-11-17.md'
assert not report.exists()
report.write_text('# Original regular auxiliary primes and local comparison\n\n'+discharged+'\n\nExact dependency: '+dependency+'\n\n'+boundary+'\n\n'+route+'\n\n'+status+'\n\nThe final consumer is `Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction.exists_gammaOne_original_unramified_adjoint_dimensions`. It retains the regular-prime and bounded-family properties on the same finite-linear-image branch and adds the original local comparison on both image branches.\n\n'+'\n'.join('- [Immutable scratch evidence]('+n+')' for n,_ in archives)+'\n',encoding='utf-8')
t=(s/'integrate_source_original_symmetric_residual_9755b.py').read_text(encoding='utf-8')
for a,b in [
    ('9725','PRIOR_SCOPE'),('9755','9783'),('PRIOR_SCOPE','9755'),
    ('source-original-symmetric-residual','source-original-auxiliary-primes'),
    ('SourceOriginalSymmetricResidual','SourceOriginalAuxiliaryPrimes'),
    ('original-symmetric-residual-20261117-2388','original-auxiliary-primes-20261117-2457'),
    ('projective-residual-image-20261117-2326','original-symmetric-residual-20261117-2388'),
    ('original-symmetric-residual-promotion-route-2388','original-auxiliary-primes-promotion-route-2457'),
    ('appliedSourceProjectiveResidualImage','appliedSourceOriginalSymmetricResidual'),
    ('Dubon Original Symmetric Residual Assessment 2026-11-17.md',report.name),
    ('(30, 30, 44, 37, 7)','(28, 28, 40, 30, 10)'),
    ('assert count == 126','assert count == 122'),
    ('"increment": 30, "queries": 44','"increment": 28, "queries": 40'),
    ('Original symmetric residual and cohomology inputs','Original regular auxiliary primes and local comparison'),
    ('SOURCE ORIGINAL SYMMETRIC RESIDUAL AUDIT PASS','SOURCE ORIGINAL AUXILIARY PRIMES AUDIT PASS'),
    ('The preceding 9,725-module scope','The preceding 9,755-module scope'),
]:
    assert a in t,a;t=t.replace(a,b)
def assignment(name,value):
    global t
    nodes=[n for n in ast.parse(t).body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id==name for x in n.targets)]
    assert len(nodes)==1,(name,len(nodes))
    n=nodes[0];lines=t.splitlines(keepends=True);lines[n.lineno-1:n.end_lineno]=[name+' = '+repr(value)+'\n'];t=''.join(lines)
for name,value in [('key','appliedSourceOriginalAuxiliaryPrimes'),('digests',digests),('dependency',dependency),('discharged',discharged),('boundary',boundary),('status',status),('route',route)]:assignment(name,value)
start=t.index('evidence=[p/n for n in ');end=t.index('\nfor cert in certs:\n    evidence.append',start)
evidence=[report.name,route_path.name]+list(digests)
for c in certs:
    for row in c['files']:evidence += [Path(row['path']).name,Path(row['compileLog']).name,Path(row['compileExit']).name]
    evidence += [Path(c['ownershipLog']).name]
for stem in ['SourceOriginalRegularPrimeScratchSemantic2406','SourceOriginalDetectingFamilyScratchSemantic2428','SourceOriginalUnramifiedDimensionScratchSemantic2435']:
    evidence += [stem+e for e in ['.lean','.log','.exit']]
t=t[:start]+'evidence=[p/n for n in '+repr(sorted(set(evidence)))+']\n'+t[end:]
old="assert sha(reportSource) == 'A9E8D1C942140C49975F87FC7DAEE4F16A707927C3E52A3F305A9CC6DB9452C3'"
assert old in t;t=t.replace(old,'assert sha(reportSource) == '+repr(sha(report)))
edge='  SYMMETRIC9755["Same original residual action: symmetric spanning, absolute irreducibility, trace-zero adjoint H0 and arithmetic twisted-H1 detection on the large-image branch. Small-image exclusions, regular primes, local conditions and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
assignment('edge',edge)
newedge='  SYMMETRIC9755["Same original residual symmetric irreducibility, adjoint H0 and twisted-H1 detection proved (DUB-17/18)"] --> AUXILIARY9783\n  AUXILIARY9783["Same original action: regular detecting primes, bounded detecting families and original unramified H1/invariant dimension comparison proved. Small-image exclusions, exact regular-prime local dimension, local deformation conditions and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
lines=t.splitlines()
for i,line in enumerate(lines):
    if line.startswith('arch.write_text('):lines[i]='arch.write_text(arch.read_text(encoding="utf-8").replace(edge,'+repr(newedge)+'),encoding="utf-8")'
t='\n'.join(lines)+'\n'
start=t.index("source = p / 'SourceOriginalResidueConsumerAudit2361.lean'")
end=t.index('(p / "source-original-auxiliary-primes-9783-production-audits.json").write_text',start)
t=t[:start]+t[end:]
t=t.replace('Original symmetric irreducibility, adjoint vanishing and arithmetic twisted-cohomology detection proved on the large-image branch.','Original regular primes, bounded detecting families and unramified H1/invariant dimension comparison proved.')
target=s/'integrate_source_original_auxiliary_primes_9783.py';assert not target.exists();ast.parse(t);target.write_text(t,encoding='utf-8')
print(json.dumps(dict(script=str(target),sha256=sha(target),scratchModules=28,exhaustiveTheorems=122,productionMutation=False)))
