from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 9725
assert d["appliedSourceProjectiveResidualImage"]["receipt9725"]["exit"] == 0
assert (p / "paper-verification-9725-console.exit").read_text().strip() == "0"
assert (r/'Tools/projective-residual-image-20261117-2326/canonical-evidence-9725.json').exists()
key = "appliedSourceOriginalSymmetricResidual"
assert key not in d
digests = {'source-original-symmetric-1-scratch-receipt.json': 'C0C6C938423119C26EBCB310EA9B5DB9A14A4CCD59507A1ACBF6A12AF04B968A', 'source-original-symmetric-adjoint-1-scratch-receipt.json': 'F1E8B92F0ED82CAB9152691D674D15BB8405E7B638324FB81DCAA4B6C0D4615C', 'source-original-twisted-kernel-1-scratch-receipt.json': '049DD5A064FC14DEFB68DA596CCF7F8A831FF30446A28C3A295843BF71EC41F0', 'source-original-symmetric-joint-1-scratch-receipt.json': '0DA618D1D4E27325F89A2C1DAEB6CCC457779E6C280A1447F57349052F814544'}

for name, digest in digests.items():
    assert sha(p / name) == digest
certs = [json.loads((p / name).read_text(encoding="utf-8")) for name in digests]
mods = [m for z in certs for m in z["modules"]]
queries = [q for z in certs for q in z["queries"]]
theorems = [q for z in certs for q in z["theoremRegistrations"]]
defs = [q for z in certs for q in z["constructionRegistrations"]]
declarationRenames = {a:b for z in certs for a,b in z.get('productionDeclarationRenames',{}).items()}
assert len(declarationRenames)==len(set(declarationRenames.values()))==0
queries=[declarationRenames.get(n,n) for n in queries]
theorems=[declarationRenames.get(n,n) for n in theorems]
defs=[declarationRenames.get(n,n) for n in defs]
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (30, 30, 44, 37, 7)
omitted = []
assert not set(mods).intersection(c["productionModules"])
mapping = {m: "Dubon2026." + m for m in c["productionModules"] + mods}
mapping["SourceGammaOneFiniteDivisorReciprocityAssembled"] = "Dubon2026.SourceGammaOneFiniteDivisorReciprocity"
# Qualify versioned imports from independently audited adjacent scratch scopes.
# Only a suffix naming a registered module is accepted; bodies/comments stay frozen.
for cert in certs:
    for item in cert['files']:
        for imported in re.findall(r'^import (\S+)',Path(item['path']).read_text(encoding='utf-8'),re.M):
            if imported in mapping or imported.startswith(('Dubon2026.','Mathlib.')):continue
            match=re.fullmatch(r'(Source.+?)([0-9]{4}[a-z]?)',imported)
            if match and match[1] in mods:mapping[imported]='Dubon2026.'+match[1]
for cert in certs:
    for source in [Path(cert['dependencyAuditLog']).with_suffix('.lean')] + [Path(x['path']) for x in cert['files']]:
        for imported in re.findall(r'\b(Source[A-Za-z0-9_]+)', source.read_text(encoding='utf-8')):
            match = re.fullmatch(r'(Source.+?)([0-9]{4}[a-z]?)', imported)
            if match and match[1] in mapping: mapping[imported] = mapping[match[1]]
newmods = [mapping[m] for m in mods]

comments = {}
pending, reviews = [], []
for z in certs:
    assert z["exit"] == z["diagnostics"] == 0
    for fname, hname in [("log", "logSha256"), ("dependencyAuditLog", "dependencyAuditSha256"),
                        ("reuseReview", "reuseReviewSha256")]:
        assert sha(Path(z[fname])) == z[hname]
    assert sha(Path(z["log"]).with_suffix(".lean")) == z["auditSha256"]
    assert sha(Path(z["dependencyAuditLog"]).with_suffix(".lean")) == z["dependencyAuditSourceSha256"]
    review = Path(z["reuseReview"])
    assert not (r / "Tools" / review.name).exists()
    reviews.append(review)
    for item in z["files"]:
        f = Path(item["path"])
        assert sha(f) == item["sha256"] and sha(f.with_suffix(".olean")) == item["oleanSha256"]
        assert Path(item["compileExit"]).read_text().strip() == "0" and Path(item["compileLog"]).stat().st_size == 0
        s = re.sub(r"(?m)^import (\S+)", lambda m: "import " + mapping.get(m[1], m[1]),
                   f.read_text(encoding="utf-8"))
        # Preserve the audited Mathlib imports; qualify only project scratch imports.
        if f.stem in comments:
            for old, new in comments[f.stem]:
                assert s.count(old) == 1
                s = s.replace(old, new)
        assert not re.search(r"\b(sorry|admit|axiom|unsafe|native_decide|implemented_by)\b|set_option|nolint|trace_state", re.sub(r"--[^\n]*", "", re.sub(r"/\-.*?\-/", "", s, flags=re.S)))
        assert all(m == "Mathlib" or m.startswith(("Dubon2026.", "Mathlib.")) for m in re.findall(r"^import (\S+)", s, re.M))
        target = r / "Extension/Dubon2026" / f.name
        assert not target.exists()
        pending.append((target, s))

# Archive local evidence without creating unaudited Lean modules in Tools.
refresh_pending=[]
archive_rel='Tools/original-symmetric-residual-20261117-2388'
evidence=[p/n for n in ['Dubon Original Symmetric Residual Assessment 2026-11-17.md', 'SourceArithmeticCyclotomicSquare.exit', 'SourceArithmeticCyclotomicSquare.lean', 'SourceArithmeticCyclotomicSquare.log', 'SourceConjugateSymmetricSpanning.exit', 'SourceConjugateSymmetricSpanning.lean', 'SourceConjugateSymmetricSpanning.log', 'SourceFiniteLinearAbsoluteGalois.exit', 'SourceFiniteLinearAbsoluteGalois.lean', 'SourceFiniteLinearAbsoluteGalois.log', 'SourceFiniteLinearKernelSymmetric.exit', 'SourceFiniteLinearKernelSymmetric.lean', 'SourceFiniteLinearKernelSymmetric.log', 'SourceFiniteLinearOriginalConsequences.exit', 'SourceFiniteLinearOriginalConsequences.lean', 'SourceFiniteLinearOriginalConsequences.log', 'SourceFiniteLinearOriginalScalar.exit', 'SourceFiniteLinearOriginalScalar.lean', 'SourceFiniteLinearOriginalScalar.log', 'SourceFiniteLinearOriginalSpanning.exit', 'SourceFiniteLinearOriginalSpanning.lean', 'SourceFiniteLinearOriginalSpanning.log', 'SourceFiniteLinearSymmetric.exit', 'SourceFiniteLinearSymmetric.lean', 'SourceFiniteLinearSymmetric.log', 'SourceFiniteLinearTwistedKernel.exit', 'SourceFiniteLinearTwistedKernel.lean', 'SourceFiniteLinearTwistedKernel.log', 'SourceFiniteSubfieldIrreducible.exit', 'SourceFiniteSubfieldIrreducible.lean', 'SourceFiniteSubfieldIrreducible.log', 'SourceGammaOneAbsoluteCyclotomicResidual.exit', 'SourceGammaOneAbsoluteCyclotomicResidual.lean', 'SourceGammaOneAbsoluteCyclotomicResidual.log', 'SourceGammaOneAbsoluteSymmetricResidual.exit', 'SourceGammaOneAbsoluteSymmetricResidual.lean', 'SourceGammaOneAbsoluteSymmetricResidual.log', 'SourceGammaOneArithmeticTwistedDetection.exit', 'SourceGammaOneArithmeticTwistedDetection.lean', 'SourceGammaOneArithmeticTwistedDetection.log', 'SourceGammaOneCyclotomicSymmetricResidual.exit', 'SourceGammaOneCyclotomicSymmetricResidual.lean', 'SourceGammaOneCyclotomicSymmetricResidual.log', 'SourceGammaOneResidueAbsoluteSymmetric.exit', 'SourceGammaOneResidueAbsoluteSymmetric.lean', 'SourceGammaOneResidueAbsoluteSymmetric.log', 'SourceGammaOneSymmetricAdjointVanishing.exit', 'SourceGammaOneSymmetricAdjointVanishing.lean', 'SourceGammaOneSymmetricAdjointVanishing.log', 'SourceGammaOneSymmetricKernelSpanning.exit', 'SourceGammaOneSymmetricKernelSpanning.lean', 'SourceGammaOneSymmetricKernelSpanning.log', 'SourceGammaOneSymmetricResidualCohomology.exit', 'SourceGammaOneSymmetricResidualCohomology.lean', 'SourceGammaOneSymmetricResidualCohomology.log', 'SourceGammaOneTwistedKernelDetection.exit', 'SourceGammaOneTwistedKernelDetection.lean', 'SourceGammaOneTwistedKernelDetection.log', 'SourceOriginalArithmeticTwistedDetection.exit', 'SourceOriginalArithmeticTwistedDetection.lean', 'SourceOriginalArithmeticTwistedDetection.log', 'SourceOriginalResidueConsumerAudit2361.exit', 'SourceOriginalResidueConsumerAudit2361.lean', 'SourceOriginalResidueConsumerAudit2361.log', 'SourceOriginalSymmetricAbsolute.exit', 'SourceOriginalSymmetricAbsolute.lean', 'SourceOriginalSymmetricAbsolute.log', 'SourceOriginalSymmetricAdjoint.exit', 'SourceOriginalSymmetricAdjoint.lean', 'SourceOriginalSymmetricAdjoint.log', 'SourceOriginalSymmetricAdjointDeclarations2366.log', 'SourceOriginalSymmetricAdjointScratchSemantic2375.exit', 'SourceOriginalSymmetricAdjointScratchSemantic2375.lean', 'SourceOriginalSymmetricAdjointScratchSemantic2375.log', 'SourceOriginalSymmetricDeclarations2354.log', 'SourceOriginalSymmetricJointDeclarations2383.log', 'SourceOriginalSymmetricJointScratchSemantic2385.exit', 'SourceOriginalSymmetricJointScratchSemantic2385.lean', 'SourceOriginalSymmetricJointScratchSemantic2385.log', 'SourceOriginalSymmetricScratchSemantic2360.exit', 'SourceOriginalSymmetricScratchSemantic2360.lean', 'SourceOriginalSymmetricScratchSemantic2360.log', 'SourceOriginalSymmetricSpanningProperty.exit', 'SourceOriginalSymmetricSpanningProperty.lean', 'SourceOriginalSymmetricSpanningProperty.log', 'SourceOriginalTwistedDetectionProperty.exit', 'SourceOriginalTwistedDetectionProperty.lean', 'SourceOriginalTwistedDetectionProperty.log', 'SourceOriginalTwistedKernelDeclarations2377.log', 'SourceOriginalTwistedKernelScratchSemantic2379.exit', 'SourceOriginalTwistedKernelScratchSemantic2379.lean', 'SourceOriginalTwistedKernelScratchSemantic2379.log', 'SourceOriginalTwistedTopology.exit', 'SourceOriginalTwistedTopology.lean', 'SourceOriginalTwistedTopology.log', 'SourceResidualConjugateIrreducible.exit', 'SourceResidualConjugateIrreducible.lean', 'SourceResidualConjugateIrreducible.log', 'SourceSpanningCoefficientExtension.exit', 'SourceSpanningCoefficientExtension.lean', 'SourceSpanningCoefficientExtension.log', 'SourceSpanningIrreducibility.exit', 'SourceSpanningIrreducibility.lean', 'SourceSpanningIrreducibility.log', 'SourceSubfieldKernelIrreducible.exit', 'SourceSubfieldKernelIrreducible.lean', 'SourceSubfieldKernelIrreducible.log', 'SourceSubfieldSymmetricAbsolute.exit', 'SourceSubfieldSymmetricAbsolute.lean', 'SourceSubfieldSymmetricAbsolute.log', 'original-symmetric-residual-promotion-route-2388.json', 'source-original-residue-consumer-edges-2361.json', 'source-original-symmetric-1-scratch-receipt.json', 'source-original-symmetric-adjoint-1-scratch-receipt.json', 'source-original-symmetric-joint-1-scratch-receipt.json', 'source-original-twisted-kernel-1-scratch-receipt.json']]

for cert in certs:
    evidence.append(Path(cert['reuseReview']))

for cert in certs:
    for field in ['log','dependencyAuditLog']:
        f=Path(cert[field]); evidence.extend([f,f.with_suffix('.lean'),f.with_suffix('.exit')])
archive=[]
archiveBytes={}
for source in dict.fromkeys(evidence):
    assert source.exists(),source
    target=r/archive_rel/source.relative_to(p)
    if source.suffix in ['.lean','.md']:target=target.with_name(target.name+'.txt')
    assert not target.exists(),target
    data=source.read_bytes()
    if target in archiveBytes and archiveBytes[target]!=data:
        target=target.with_name(target.name+'.source-'+sha(source)[:16]+'.txt')
        assert not target.exists(),target
    if target in archiveBytes:assert archiveBytes[target]==data,target
    else:
        archiveBytes[target]=data
        refresh_pending.append((target,data,'Tools'))
    archive.append(dict(source=str(source),path=target.relative_to(r).as_posix(),sha256=sha(source)))
archive_target=r/archive_rel/'archive-manifest.json'
assert not archive_target.exists()
refresh_pending.append((archive_target,(json.dumps(dict(files=archive),indent=2)+'\n').encode(),'Tools'))
supplemental_review_path=r/archive_rel/'original-symmetric-residual-promotion-route-2388.json'

audit = r / "Extension/Dubon2026/Audit.lean"
at = audit.read_text(encoding="utf-8")
for n in queries:
    assert not re.search(r"``" + re.escape(n) + r"(?=[,\s])", at)
tm, dm = "\n]\n\nprivate def publicConstructions", "\n]\n\nprivate def runAudit"
assert at.count(tm) == at.count(dm) == 1
at = at.replace(tm, "".join("\n  ,``" + n for n in theorems) + tm, 1)
at = at.replace(dm, "".join("\n  ," + chr(96)*2 + n for n in defs) + dm, 1)
research_path = r / "Tools/lean-reuse-audit-20261020.json"
reuse_path = r / "Tools/source-original-symmetric-residual.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt9725"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> automorphy -> actual original residual deformation inputs -> symmetric irreducibility, trace-zero adjoint H0 and arithmetic twisted-H1 detection for the same constructed residual representation.'
discharged = 'For an actual original primitive cusp form of weight at least two and prime p greater than three, one constructed original residual representation now retains its complete projective classification and, in the finite linear subfield branch, has full symmetric matrix spans, absolute symmetric-power irreducibility and vanishing trace-zero adjoint invariants over its original residue field and basis on both native arithmetic and absolute Galois cyclotomic kernels. These conclusions hold for 2*n < p-1. The same residual representation has genuine arithmetic twisted-cohomology detection on the joint residual/cyclotomic kernel in every symmetric degree. Its integral origin, literal reduction, fixed-local Hecke/Frobenius and inertia data, global determinant, maximal Hecke kernel, finite image and oddness are retained. No image classification, irreducibility, adjoint-vanishing, character-value witness or cohomology-detection certificate is supplied.'
boundary = 'The six small-projective-image alternatives are retained explicitly; their arithmetic exclusion, regular detecting primes and the remaining original local conditions are still required. The finite subfield is not identified with the original residue field. Finite-image H1 vanishing has not been proved and is not an extra prerequisite of the central-scalar detection route. These source consumers still have weight at least two and p greater than three. Automorphy and literal higher symmetric-power continuation remain open. Acceptance remains 16/20; DUB-17--20 OPEN, with the full source domain and every verification criterion unchanged.'
status = 'The 30-module scratch scope passes 44 public axiom queries, all 126 theorem and 52 other declaration checks, sixteen linters per module, exact ownership enumeration and 178 declaration type/value fingerprints. Four source proof-value audits verify 258 required dependency checks, with a separate 26-edge final-original-consumer audit. Production aggregate, focused audits and sequential foundation/paper verification of the 9,755-module scope are pending.'
route = 'Reuse the already proved native finite-subfield symmetric span, perfection of SL2, coefficient-extension/descent, Schur adjoint vanishing, central-scalar cocycle detection and actual arithmetic cyclotomic surjectivity. Full matrix spanning descends through an explicit coefficient left inverse, so neither coefficient-field equality nor a separately supplied change-of-basis certificate is needed. The central-scalar argument avoids a separate finite-image H1 vanishing development for this detection step. Generic proofs are applied to the same residual witness and literally the native arithmetic cyclotomic character; independent existential witnesses are never identified. The upstream Dickson classification is already integrated. No additional external imports, pins, proof-limit changes or incidental generalizations are introduced.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Original symmetric residual and cohomology inputs (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 9,725-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
corrections = []
count = sum(z['exhaustiveTheorems'] for z in certs)
assert count == 126

docpaths = list(dict.fromkeys(r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]))
for f in docpaths:
    assert "\n\n" in f.read_text(encoding="utf-8")
readmes = [(r.parent / "README.md", "Current Project 83 status ("), (repo / "README.md", "Project 83 has an ")]
for f, prefix in readmes:
    assert sum(line.startswith(prefix) for line in f.read_text(encoding="utf-8").splitlines()) == 1
arch = r / "Dubon Architecture.md"
edge = '  PROJECTIVE9725["Original projective classification, explicit conjugacy and literal SL2/scalar-GL2 bounds over a finite coefficient extension proved. Six small-image exclusions, local regularity and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourceOriginalSymmetricResidualProductionAudit9755.lean',p/'source-original-symmetric-residual-9755-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production9755.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/projective-residual-image-20261117-2326'
registered = {row['path'] for row in c['files']}
for priorFile in priorArchive.iterdir():
    rel = priorFile.relative_to(r).as_posix()
    if priorFile.is_file() and rel not in registered:
        c['files'].append({'path': rel, 'role': 'Tools'})

reportSource = p / 'Dubon Original Symmetric Residual Assessment 2026-11-17.md'
assert sha(reportSource) == 'A9E8D1C942140C49975F87FC7DAEE4F16A707927C3E52A3F305A9CC6DB9452C3'
reportTarget = r / reportSource.name
assert not reportTarget.exists()

# All frozen source, receipt and document checks precede production mutation.
for target, data, role in refresh_pending:
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(data)
    c['files'].append({'path': target.relative_to(r).as_posix(), 'role': role})
for target, s in pending:
    target.write_text(s, encoding="utf-8")
    c["productionModules"].append(target.stem)
    c["files"].append({"path": target.relative_to(r).as_posix(), "role": "Extension"})
root = r / "Extension/Dubon2026.lean"
root.write_text(root.read_text(encoding="utf-8") + "".join("import " + m + "\n" for m in newmods), encoding="utf-8")
audit.write_text(at, encoding="utf-8")
for f in reviews:
    target = r / "Tools" / f.name
    target.write_bytes(f.read_bytes())
    c["files"].append({"path": target.relative_to(r).as_posix(), "role": "Tools"})
reuse = {"date": dateLabel, "modules": newmods, "dependency": dependency,
    "discharged": discharged, "boundary": boundary, "status": status, "rootPinsChanged": False,
    "proofLimitsChanged": False, "frozenReceiptProseCorrections": corrections, "sourceConsumers": [n for z in certs for n in z["consumers"]],
    "scratchCertificates": certs, "reviews": ["Tools/" + f.name for f in reviews]}
reuse['productionDeclarationRenames'] = declarationRenames
reuse['dependencyRouteAssessment'] = dict(path=supplemental_review_path.relative_to(r).as_posix(),sha256=sha(supplemental_review_path))
reuse['proofEvidenceArchive'] = dict(manifest=archive_target.relative_to(r).as_posix(),sha256=sha(archive_target),externalLocalBuild=False,externalImport=False)
reuse_path.write_text(json.dumps(reuse, indent=2) + "\n", encoding="utf-8")
c["files"].append({"path": reuse_path.relative_to(r).as_posix(), "role": "Tools"})
reportTarget.write_bytes(reportSource.read_bytes())
c['files'].append({'path': reportTarget.name, 'role': 'root'})
cp.write_text(json.dumps(c, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
d[key] = {"recordedUTC": datetime.now(timezone.utc).isoformat(), "date": dateLabel,
    "productionModules": 9755, "modules": newmods, "queries": queries,
    "theoremRegistrations": theorems, "constructionRegistrations": defs,
    "sourceHashes": {mapping[t.stem]: sha(t) for t, _ in pending}, "scratchCertificates": certs,
    "exactDependency": dependency, "assumptionsDischarged": discharged, "stillOpen": boundary,
    "status": status, "rootPinsChanged": False, "proofLimitsChanged": False,
    "promotionChanges": 'Only scratch imports are qualified to registered production modules. All audited statements, proof bodies and comments remain identical. Exact ownership and normalized type/value reconciliation are mandatory. The same actual original residual representation carries every stated consequence; no assumption or completion criterion is weakened.',
    "omittedScratchTheorems": omitted,
    "existingReuseTheorems": [], "productionDeclarationRenames": declarationRenames,
    "reuseMetadata": reuse_path.relative_to(r).as_posix(), "review": research_path.relative_to(r).as_posix()}
dp.write_text(json.dumps(d, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
research = {**reuse, "currentApplication": reuse_path.relative_to(r).as_posix(),
    "metadata": "Tools/lean-reuse-audit-20261015.json#" + key, "previousApplication": oldresearch,
    "researchConclusion": discharged + " " + boundary}


research_path.write_text(json.dumps(research, indent=2) + "\n", encoding="utf-8")
for f in docpaths:
    first, rest = f.read_text(encoding="utf-8").split("\n\n", 1)
    f.write_text(first + "\n\n" + note + "\n\nEarlier dated implementation paragraphs are historical "
        "checkpoints; the current mathematical scope is stated above.\n\n" + rest, encoding="utf-8")
arch.write_text(arch.read_text(encoding="utf-8").replace(edge,'  PROJECTIVE9725["Actual projective classification and finite linear subfield bounds constructed (DUB-17/18)"] --> SYMMETRIC9755\n  SYMMETRIC9755["Same original residual action: symmetric spanning, absolute irreducibility, trace-zero adjoint H0 and arithmetic twisted-H1 detection on the large-image branch. Small-image exclusions, regular primes, local conditions and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'),encoding="utf-8")



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Original symmetric residual and cohomology inputs - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-original-symmetric-residual.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub('  logInfo m!".*"\n', '  logInfo m!"SOURCE ORIGINAL SYMMETRIC RESIDUAL AUDIT PASS: {count} theorems including private/generated declarations. Original symmetric irreducibility, adjoint vanishing and arithmetic twisted-cohomology detection proved on the large-image branch. Remaining association and higher continuation OPEN;16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourceOriginalSymmetricResidualProductionAudit9755.lean").write_text(out, encoding="utf-8")
audits = []
for z in certs:
    source = Path(z["dependencyAuditLog"]).with_suffix(".lean")
    s = source.read_text(encoding="utf-8")
    if source.stem == 'SourceOriginalPrimeDependencyAudit':
        s = s.replace('`Dubon2026.SourceFunctionField.laurentBaseChange_adjoin,',
                      '`Dubon2026.SourceFunctionField.laurentBaseChange_full_eq_adjoin,')
    for old, new in mapping.items():
        s = re.sub(r"(?m)^import " + re.escape(old) + r"$", "import " + new, s)
        s = re.sub(r"`" + re.escape(old) + r"(?=[,\]\s])", "`" + new, s)
    target = p / (source.stem + "Production9755.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
source = p / 'SourceOriginalResidueConsumerAudit2361.lean'
s = source.read_text(encoding='utf-8')
for old, new in mapping.items():
    s = re.sub(r'(?m)^import ' + re.escape(old) + r'$', 'import ' + new, s)
    s = re.sub(r'`' + re.escape(old) + r'(?=[,\]\s])', '`' + new, s)
target = p / 'SourceOriginalResidueConsumerProductionAudit9755.lean'
assert not target.exists(); target.write_text(s,encoding='utf-8')

(p / "source-original-symmetric-residual-9755-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 9755, "increment": 30, "queries": 44,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
