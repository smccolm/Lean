from pathlib import Path
import ast, hashlib, json, re

s = Path(__file__).parent
p = Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
digests = {
    'source-original-symmetric-1-scratch-receipt.json': 'C0C6C938423119C26EBCB310EA9B5DB9A14A4CCD59507A1ACBF6A12AF04B968A',
    'source-original-symmetric-adjoint-1-scratch-receipt.json': 'F1E8B92F0ED82CAB9152691D674D15BB8405E7B638324FB81DCAA4B6C0D4615C',
    'source-original-twisted-kernel-1-scratch-receipt.json': '049DD5A064FC14DEFB68DA596CCF7F8A831FF30446A28C3A295843BF71EC41F0',
    'source-original-symmetric-joint-1-scratch-receipt.json': '0DA618D1D4E27325F89A2C1DAEB6CCC457779E6C280A1447F57349052F814544',
}
certs = []
for name, digest in digests.items():
    assert sha(s/name) == digest
    certs.append(json.loads((s/name).read_text()))
modules = [m for c in certs for m in c['modules']]
assert len(modules) == len(set(modules)) == 30
assert sum(len(c['queries']) for c in certs) == 44
assert sum(len(c['theoremRegistrations']) for c in certs) == 37
assert sum(len(c['constructionRegistrations']) for c in certs) == 7
assert sum(c['exhaustiveTheorems'] for c in certs) == 126
assert sum(c['exhaustiveOtherDeclarations'] for c in certs) == 52
assert sum(c['requiredProofValueEdges'] for c in certs) == 258
archives = [
    'Tools/original-symmetric-scratch-20261117-2359/manifest.json',
    'Tools/original-symmetric-adjoint-scratch-20261117-2376/manifest.json',
    'Tools/original-twisted-kernel-scratch-20261117-2380/manifest.json',
    'Tools/original-symmetric-joint-scratch-20261117-2386/manifest.json',
]
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> automorphy -> actual original residual deformation inputs -> symmetric irreducibility, trace-zero adjoint H0 and arithmetic twisted-H1 detection for the same constructed residual representation.'
discharged = ('For an actual original primitive cusp form of weight at least two and prime p greater than three, one constructed original residual representation now retains its complete projective classification and, in the finite linear subfield branch, has full symmetric matrix spans, absolute symmetric-power irreducibility and vanishing trace-zero adjoint invariants over its original residue field and basis on both native arithmetic and absolute Galois cyclotomic kernels. These conclusions hold for 2*n < p-1. The same residual representation has genuine arithmetic twisted-cohomology detection on the joint residual/cyclotomic kernel in every symmetric degree. Its integral origin, literal reduction, fixed-local Hecke/Frobenius and inertia data, global determinant, maximal Hecke kernel, finite image and oddness are retained. No image classification, irreducibility, adjoint-vanishing, character-value witness or cohomology-detection certificate is supplied.')
boundary = ('The six small-projective-image alternatives are retained explicitly; their arithmetic exclusion, regular detecting primes and the remaining original local conditions are still required. The finite subfield is not identified with the original residue field. Finite-image H1 vanishing has not been proved and is not an extra prerequisite of the central-scalar detection route. These source consumers still have weight at least two and p greater than three. Automorphy and literal higher symmetric-power continuation remain open. Acceptance remains 16/20; DUB-17--20 OPEN, with the full source domain and every verification criterion unchanged.')
status = ('The 30-module scratch scope passes 44 public axiom queries, all 126 theorem and 52 other declaration checks, sixteen linters per module, exact ownership enumeration and 178 declaration type/value fingerprints. Four source proof-value audits verify 258 required dependency checks, with a separate 26-edge final-original-consumer audit. Production aggregate, focused audits and sequential foundation/paper verification of the 9,755-module scope are pending.')
route = ('Reuse the already proved native finite-subfield symmetric span, perfection of SL2, coefficient-extension/descent, Schur adjoint vanishing, central-scalar cocycle detection and actual arithmetic cyclotomic surjectivity. Full matrix spanning descends through an explicit coefficient left inverse, so neither coefficient-field equality nor a separately supplied change-of-basis certificate is needed. The central-scalar argument avoids a separate finite-image H1 vanishing development for this detection step. Generic proofs are applied to the same residual witness and literally the native arithmetic cyclotomic character; independent existential witnesses are never identified. The upstream Dickson classification is already integrated. No additional external imports, pins, proof-limit changes or incidental generalizations are introduced.')
route_path = s/'original-symmetric-residual-promotion-route-2388.json'
review = dict(dependency=dependency, discharged=discharged, boundary=boundary, route=route,
    scratchCertificates=[dict(path=n, sha256=h) for n,h in digests.items()],
    immutableScratchArchives=[dict(path=n,sha256=sha(p/n)) for n in archives],
    disjointModules=30, publicTheorems=37, publicConstructions=7,
    exhaustiveTheorems=126, exhaustiveOtherDeclarations=52, typeValueFingerprints=178,
    proofValueEdges=[c['requiredProofValueEdges'] for c in certs], separateOriginalConsumerEdges=26,
    proofBodiesPreserved=True, changes='Only import qualification during promotion.', accepted=16,total=20)
assert not route_path.exists();route_path.write_text(json.dumps(review,indent=2)+'\n')
report = s/'Dubon Original Symmetric Residual Assessment 2026-11-17.md'
assert not report.exists()
report.write_text('# Original symmetric residual and cohomology inputs\n\n'+discharged+'\n\nExact dependency: '+dependency+'\n\n'+boundary+'\n\n'+route+'\n\n'+status+'\n\nThe final consumer is `Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction.exists_gammaOne_original_symmetric_residual_cohomology`. Its large-image conclusions concern one and the same constructed residual action, not separately selected witnesses. The four independently audited scopes have 18, 2, 8 and 2 modules.\n\n'+ '\n'.join('- [Immutable scratch evidence]('+x+')' for x in archives)+'\n',encoding='utf-8')

# Derive the promotion transaction from the preceding reviewed transaction;
# change complete assignment values, not individual proof bodies or source text.
t=(s/'integrate_source_projective_residual_image_9725.py').read_text()
for a,b in [('9697','PRIOR_SCOPE'),('9725','9755'),('PRIOR_SCOPE','9725'),
 ('9,697','9,725'),('9,725-module scope passed','9,725-module scope passed'),
 ('appliedSourceOriginalRankTwo','appliedSourceProjectiveResidualImage'),
 ('original-rank-two-residual-20261117-2268','projective-residual-image-20261117-2326'),
 ('appliedSourceProjectiveResidualImage"\nassert key','appliedSourceOriginalSymmetricResidual"\nassert key'),
 ('source-projective-residual-image','source-original-symmetric-residual'),
 ('SourceProjectiveResidualImage','SourceOriginalSymmetricResidual'),
 ('projective-residual-image-20261117-2326\'\nevidence','original-symmetric-residual-20261117-2388\'\nevidence'),
 ('projective-residual-image-promotion-route-2326','original-symmetric-residual-promotion-route-2388'),
 ('Dubon Projective Residual Image Assessment 2026-11-17.md','Dubon Original Symmetric Residual Assessment 2026-11-17.md')]:t=t.replace(a,b)
t=t.replace('==3\nqueries=', '==0\nqueries=')
t=t.replace('(28, 28, 436, 371, 65)', '(30, 30, 44, 37, 7)')
t=t.replace('assert count == 939','assert count == 126')
t=t.replace('"increment": 28, "queries": 436','"increment": 30, "queries": 44')

def assignment(name,value):
    global t
    tree=ast.parse(t)
    nodes=[n for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(x,ast.Name) and x.id==name for x in n.targets)]
    assert len(nodes)==1,(name,len(nodes))
    n=nodes[0];lines=t.splitlines(keepends=True)
    lines[n.lineno-1:n.end_lineno]=[name+' = '+repr(value)+'\n'];t=''.join(lines)

for name,value in [('digests',digests),('dependency',dependency),('discharged',discharged),('boundary',boundary),('status',status),('route',route)]:assignment(name,value)
start=t.index('evidence=[p/n for n in ')
end=t.index('\nfor cert in certs:\n    evidence.append',start)
evidence=[report.name,route_path.name]+list(digests)
for c in certs:
    for row in c['files']:
        evidence += [Path(row['path']).name,Path(row['compileLog']).name,Path(row['compileExit']).name]
    evidence += [Path(c['ownershipLog']).name]
for stem in ['SourceOriginalSymmetricScratchSemantic2360','SourceOriginalSymmetricAdjointScratchSemantic2375','SourceOriginalTwistedKernelScratchSemantic2379','SourceOriginalSymmetricJointScratchSemantic2385','SourceOriginalResidueConsumerAudit2361']:
    evidence += [stem+e for e in ['.lean','.log','.exit']]
evidence += ['source-original-residue-consumer-edges-2361.json']
t=t[:start]+'evidence=[p/n for n in '+repr(sorted(set(evidence)))+']\n'+t[end:]
t=t.replace("'Original projective residual image and finite linear bounds ('", "'Original symmetric residual and cohomology inputs ('")
t=t.replace("'Original projective residual image and finite linear bounds - '","'Original symmetric residual and cohomology inputs - '")
t=t.replace('## Original projective residual image and finite linear bounds - ', '## Original symmetric residual and cohomology inputs - ')
t=t.replace('SOURCE PROJECTIVE RESIDUAL IMAGE AUDIT PASS', 'SOURCE ORIGINAL SYMMETRIC RESIDUAL AUDIT PASS')
t=t.replace('Original projective residual image and finite linear bounds with exact Fourier Frobenius values proved.', 'Original symmetric irreducibility, adjoint vanishing and arithmetic twisted-cohomology detection proved on the large-image branch.')
t=t.replace('Only scratch imports are qualified to registered production modules. All audited statements, proof bodies and comments remain identical. Three compiler-generated public prime-instance names change under the production module prefix; the exact names were independently compiled and enumerated, and ownership/type/value comparison is mandatory. Actual modular forms and their original arithmetic data are retained; no assumption or completion criterion is weakened.', 'Only scratch imports are qualified to registered production modules. All audited statements, proof bodies and comments remain identical. Exact ownership and normalized type/value reconciliation are mandatory. The same actual original residual representation carries every stated consequence; no assumption or completion criterion is weakened.')
t=t.replace("assert sha(reportSource) == 'E0FE687B1349242CCF8F85782430B9AC8D6791848700C387A86431535DC22C74'",'assert sha(reportSource) == '+repr(sha(report)))
old_edge='  PROJECTIVE9725["Original projective classification, explicit conjugacy and literal SL2/scalar-GL2 bounds over a finite coefficient extension proved. Six small-image exclusions, local regularity and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
new_edge='  PROJECTIVE9725["Actual projective classification and finite linear subfield bounds constructed (DUB-17/18)"] --> SYMMETRIC9755\n  SYMMETRIC9755["Same original residual action: symmetric spanning, absolute irreducibility, trace-zero adjoint H0 and arithmetic twisted-H1 detection on the large-image branch. Small-image exclusions, regular primes, local conditions and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
assignment('edge',old_edge)
lines=t.splitlines()
for i,line in enumerate(lines):
    if line.startswith('arch.write_text('):lines[i]='arch.write_text(arch.read_text(encoding="utf-8").replace(edge,'+repr(new_edge)+'),encoding="utf-8")'
t='\n'.join(lines)+'\n'
# The additional final-original consumer is an independent retained audit.
needle='(p / "source-original-symmetric-residual-9755-production-audits.json").write_text'
assert t.count(needle)==1
extra='''source = p / 'SourceOriginalResidueConsumerAudit2361.lean'
s = source.read_text(encoding='utf-8')
for old, new in mapping.items():
    s = re.sub(r'(?m)^import ' + re.escape(old) + r'$', 'import ' + new, s)
    s = re.sub(r'`' + re.escape(old) + r'(?=[,\\]\\s])', '`' + new, s)
target = p / 'SourceOriginalResidueConsumerProductionAudit9755.lean'
assert not target.exists(); target.write_text(s,encoding='utf-8')
'''
t=t.replace(needle,extra+'\n'+needle)
target=s/'integrate_source_original_symmetric_residual_9755.py';assert not target.exists()
ast.parse(t);target.write_text(t)
print(json.dumps(dict(script=str(target),sha256=sha(target),reportSha256=sha(report),scratchModules=len(modules),exhaustiveTheorems=126,productionMutation=False)))
