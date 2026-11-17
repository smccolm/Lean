from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 9755
assert d["appliedSourceOriginalSymmetricResidual"]["receipt9755"]["exit"] == 0
assert (p / "paper-verification-9755-console.exit").read_text().strip() == "0"
assert (r/'Tools/original-symmetric-residual-20261117-2388/canonical-evidence-9755.json').exists()
key = 'appliedSourceOriginalAuxiliaryPrimes'
assert key not in d
digests = {'source-original-regular-prime-1-scratch-receipt.json': '334EF60FE3B73F047A5F481753159A204503CB6CCD035A70D9244A3F96A75A48', 'source-original-detecting-family-2-scratch-receipt.json': 'D6EB8D8B5AB21272E5771AD1308CD4E8073DB28E82D4DF967FE3709B147F10C8', 'source-original-unramified-dimension-1-scratch-receipt.json': 'E52346CFD7BCEB752F11156364F26F09705DDB99034F137448DFE5810B7A228D'}

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
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (28, 28, 40, 30, 10)
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
archive_rel='Tools/original-auxiliary-primes-20261117-2457'
evidence=[p/n for n in ['Dubon Original Auxiliary Primes Assessment 2026-11-17.md', 'SourceFiniteLinearOriginalRegularDetection.exit', 'SourceFiniteLinearOriginalRegularDetection.lean', 'SourceFiniteLinearOriginalRegularDetection.log', 'SourceGammaOneOriginalDetectingFamilies.exit', 'SourceGammaOneOriginalDetectingFamilies.lean', 'SourceGammaOneOriginalDetectingFamilies.log', 'SourceGammaOneOriginalRegularPrimes.exit', 'SourceGammaOneOriginalRegularPrimes.lean', 'SourceGammaOneOriginalRegularPrimes.log', 'SourceGammaOneOriginalUnramifiedDimensions.exit', 'SourceGammaOneOriginalUnramifiedDimensions.lean', 'SourceGammaOneOriginalUnramifiedDimensions.log', 'SourceOriginalArithmeticFamilyProperty.exit', 'SourceOriginalArithmeticFamilyProperty.lean', 'SourceOriginalArithmeticFamilyProperty.log', 'SourceOriginalArithmeticRegularCocycle.exit', 'SourceOriginalArithmeticRegularCocycle.lean', 'SourceOriginalArithmeticRegularCocycle.log', 'SourceOriginalArithmeticRegularPrimeProperty.exit', 'SourceOriginalArithmeticRegularPrimeProperty.lean', 'SourceOriginalArithmeticRegularPrimeProperty.log', 'SourceOriginalArithmeticRegularPrimes.exit', 'SourceOriginalArithmeticRegularPrimes.lean', 'SourceOriginalArithmeticRegularPrimes.log', 'SourceOriginalArithmeticRootKernel.exit', 'SourceOriginalArithmeticRootKernel.lean', 'SourceOriginalArithmeticRootKernel.log', 'SourceOriginalClassPrimePredicates.exit', 'SourceOriginalClassPrimePredicates.lean', 'SourceOriginalClassPrimePredicates.log', 'SourceOriginalClassRegularPrimes.exit', 'SourceOriginalClassRegularPrimes.lean', 'SourceOriginalClassRegularPrimes.log', 'SourceOriginalCocycleClassPrimes.exit', 'SourceOriginalCocycleClassPrimes.lean', 'SourceOriginalCocycleClassPrimes.log', 'SourceOriginalCoefficientH1Finite.exit', 'SourceOriginalCoefficientH1Finite.lean', 'SourceOriginalCoefficientH1Finite.log', 'SourceOriginalDetectingFamilyDeclarations2427.log', 'SourceOriginalDetectingFamilyProperty.exit', 'SourceOriginalDetectingFamilyProperty.lean', 'SourceOriginalDetectingFamilyProperty.log', 'SourceOriginalDetectingFamilyScratchSemantic2428.exit', 'SourceOriginalDetectingFamilyScratchSemantic2428.lean', 'SourceOriginalDetectingFamilyScratchSemantic2428.log', 'SourceOriginalExtendedTraceTest.exit', 'SourceOriginalExtendedTraceTest.lean', 'SourceOriginalExtendedTraceTest.log', 'SourceOriginalFiniteDetectingFamily.exit', 'SourceOriginalFiniteDetectingFamily.lean', 'SourceOriginalFiniteDetectingFamily.log', 'SourceOriginalLocalCoefficientH1Finite.exit', 'SourceOriginalLocalCoefficientH1Finite.lean', 'SourceOriginalLocalCoefficientH1Finite.log', 'SourceOriginalLocalUnramifiedDimension.exit', 'SourceOriginalLocalUnramifiedDimension.lean', 'SourceOriginalLocalUnramifiedDimension.log', 'SourceOriginalPrimeUnramifiedDimension.exit', 'SourceOriginalPrimeUnramifiedDimension.lean', 'SourceOriginalPrimeUnramifiedDimension.log', 'SourceOriginalRegularPrimeAssembly.exit', 'SourceOriginalRegularPrimeAssembly.lean', 'SourceOriginalRegularPrimeAssembly.log', 'SourceOriginalRegularPrimeDeclarations2405.log', 'SourceOriginalRegularPrimePredicates.exit', 'SourceOriginalRegularPrimePredicates.lean', 'SourceOriginalRegularPrimePredicates.log', 'SourceOriginalRegularPrimeScratchSemantic2406.exit', 'SourceOriginalRegularPrimeScratchSemantic2406.lean', 'SourceOriginalRegularPrimeScratchSemantic2406.log', 'SourceOriginalUnramifiedAdjointProperty.exit', 'SourceOriginalUnramifiedAdjointProperty.lean', 'SourceOriginalUnramifiedAdjointProperty.log', 'SourceOriginalUnramifiedDimensionDeclarations2434.log', 'SourceOriginalUnramifiedDimensionScratchSemantic2435.exit', 'SourceOriginalUnramifiedDimensionScratchSemantic2435.lean', 'SourceOriginalUnramifiedDimensionScratchSemantic2435.log', 'SourcePrimeIndexedDetectingFamily.exit', 'SourcePrimeIndexedDetectingFamily.lean', 'SourcePrimeIndexedDetectingFamily.log', 'SourceSubfieldProjectorSpan.exit', 'SourceSubfieldProjectorSpan.lean', 'SourceSubfieldProjectorSpan.log', 'SourceSubfieldRegularKernel.exit', 'SourceSubfieldRegularKernel.lean', 'SourceSubfieldRegularKernel.log', 'SourceSubfieldRegularTrace.exit', 'SourceSubfieldRegularTrace.lean', 'SourceSubfieldRegularTrace.log', 'SourceTraceZeroCoefficientEmbedding.exit', 'SourceTraceZeroCoefficientEmbedding.lean', 'SourceTraceZeroCoefficientEmbedding.log', 'SourceTraceZeroConjugacy.exit', 'SourceTraceZeroConjugacy.lean', 'SourceTraceZeroConjugacy.log', 'original-auxiliary-primes-promotion-route-2457.json', 'source-original-detecting-family-2-scratch-receipt.json', 'source-original-regular-prime-1-scratch-receipt.json', 'source-original-unramified-dimension-1-scratch-receipt.json']]

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
supplemental_review_path=r/archive_rel/'original-auxiliary-primes-promotion-route-2457.json'

audit = r / "Extension/Dubon2026/Audit.lean"
at = audit.read_text(encoding="utf-8")
for n in queries:
    assert not re.search(r"``" + re.escape(n) + r"(?=[,\s])", at)
tm, dm = "\n]\n\nprivate def publicConstructions", "\n]\n\nprivate def runAudit"
assert at.count(tm) == at.count(dm) == 1
at = at.replace(tm, "".join("\n  ,``" + n for n in theorems) + tm, 1)
at = at.replace(dm, "".join("\n  ," + chr(96)*2 + n for n in defs) + dm, 1)
research_path = r / "Tools/lean-reuse-audit-20261020.json"
reuse_path = r / "Tools/source-original-auxiliary-primes.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt9755"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> automorphy -> actual original residual deformation inputs -> regular auxiliary-prime detection, bounded jointly detecting families and original-field unramified adjoint dimension comparison.'
discharged = 'For an actual original primitive cusp form of weight at least two and prime p greater than three, the same constructed residual representation retains all its original integral, reduction, Hecke, Frobenius, determinant and oddness data. In its finite linear subfield branch, every nonzero original symmetric twisted-H1 class with 2*n < p-1 has regular detecting primes outside any finite set and congruent to one modulo every prescribed p-power. The actual common finite affine factor, unramified Frobenius and nonzero original localization are constructed. Every subspace of the original global H1 has a jointly detecting family of cardinality at most its original-field dimension; global H1 finiteness is derived rather than supplied. For every symmetric degree and every rational prime, the original local unramified adjoint H1 dimension equals the actual invariant-space dimension, without a large-image assumption. All prior conclusions concern the same original representation.'
boundary = 'The six small-projective-image alternatives remain explicit and their arithmetic exclusion is still required. The regular-prime invariant dimension is not yet computed in this promoted scope; original local deformation conditions, automorphy and literal higher symmetric-power continuation remain open. The finite subfield is not identified with the original residue field. The actual-form consumer retains weight at least two and p greater than three; full source-domain obligations remain. Acceptance remains 16/20; DUB-17--20 OPEN, with every source and verification criterion unchanged.'
status = 'The 28-module scratch scope passes 40 public axiom queries, all 122 theorem and 25 other declaration checks, sixteen linters per module, exact ownership enumeration and 147 declaration type/value fingerprints. Three source proof-value audits verify 123, 138 and 151 required dependencies, respectively. Production aggregate, focused audits and sequential foundation/paper verification of the 9,783-module scope are pending.'
route = 'Reuse native subfield projectors, perfect SL2 kernels, the original cyclotomic root-fixing argument and genuine conjugate Chebotarev. Original non-coboundary detection avoids a separate H1 scalar-extension comparison. Restricting coefficient scalars injects the same global and local continuous cocycles into already proved finite prime-field cocycle spaces; the original H1 quotient is finite. Native finite_detecting_family_of_pointwise constructs the bounded family. The existing finite-field cyclic-depth theorem proves the original unramified H1/invariant dimension formula. No additional external import, root-pin change, proof-limit change, general cohomology base-change theory or independent image certificate is introduced.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Original regular auxiliary primes and local comparison (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 9,755-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
corrections = []
count = sum(z['exhaustiveTheorems'] for z in certs)
assert count == 122

docpaths = list(dict.fromkeys(r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]))
for f in docpaths:
    assert "\n\n" in f.read_text(encoding="utf-8")
readmes = [(r.parent / "README.md", "Current Project 83 status ("), (repo / "README.md", "Project 83 has an ")]
for f, prefix in readmes:
    assert sum(line.startswith(prefix) for line in f.read_text(encoding="utf-8").splitlines()) == 1
arch = r / "Dubon Architecture.md"
edge = '  SYMMETRIC9755["Same original residual action: symmetric spanning, absolute irreducibility, trace-zero adjoint H0 and arithmetic twisted-H1 detection on the large-image branch. Small-image exclusions, regular primes, local conditions and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourceOriginalAuxiliaryPrimesProductionAudit9783.lean',p/'source-original-auxiliary-primes-9783-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production9783.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/original-symmetric-residual-20261117-2388'
registered = {row['path'] for row in c['files']}
for priorFile in priorArchive.iterdir():
    rel = priorFile.relative_to(r).as_posix()
    if priorFile.is_file() and rel not in registered:
        c['files'].append({'path': rel, 'role': 'Tools'})

reportSource = p / 'Dubon Original Auxiliary Primes Assessment 2026-11-17.md'
assert sha(reportSource) == '161115DB2CDCE013389875FAC78DCA73488271C163BDCF73155AF734BE3A3451'
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
    "productionModules": 9783, "modules": newmods, "queries": queries,
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
arch.write_text(arch.read_text(encoding="utf-8").replace(edge,'  SYMMETRIC9755["Same original residual symmetric irreducibility, adjoint H0 and twisted-H1 detection proved (DUB-17/18)"] --> AUXILIARY9783\n  AUXILIARY9783["Same original action: regular detecting primes, bounded detecting families and original unramified H1/invariant dimension comparison proved. Small-image exclusions, exact regular-prime local dimension, local deformation conditions and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'),encoding="utf-8")



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Original regular auxiliary primes and local comparison - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-original-auxiliary-primes.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub('  logInfo m!".*"\n', '  logInfo m!"SOURCE ORIGINAL AUXILIARY PRIMES AUDIT PASS: {count} theorems including private/generated declarations. Original regular primes, bounded detecting families and unramified H1/invariant dimension comparison proved. Remaining association and higher continuation OPEN;16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourceOriginalAuxiliaryPrimesProductionAudit9783.lean").write_text(out, encoding="utf-8")
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
    target = p / (source.stem + "Production9783.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
(p / "source-original-auxiliary-primes-9783-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 9783, "increment": 28, "queries": 40,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
