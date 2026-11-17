from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 9697
assert d["appliedSourceOriginalRankTwo"]["receipt9697"]["exit"] == 0
assert (p / "paper-verification-9697-console.exit").read_text().strip() == "0"
assert (r/'Tools/original-rank-two-residual-20261117-2268/canonical-evidence-9697.json').exists()
key = "appliedSourceProjectiveResidualImage"
assert key not in d
digests = {'source-projective-linear-normalized-1-scratch-receipt.json': '8CD6B02E4E0B7A5F1A5E18A1C853DEF053B73529A505DF9ADCFF2D67497EDB33', 'source-projective-finite-normalized-1-scratch-receipt.json': 'B490938772C25A888E984B6B964D091E12134A31A7F1ADB4B7F5CFBDFF3E677B'}

for name, digest in digests.items():
    assert sha(p / name) == digest
certs = [json.loads((p / name).read_text(encoding="utf-8")) for name in digests]
mods = [m for z in certs for m in z["modules"]]
queries = [q for z in certs for q in z["queries"]]
theorems = [q for z in certs for q in z["theoremRegistrations"]]
defs = [q for z in certs for q in z["constructionRegistrations"]]
declarationRenames = {a:b for z in certs for a,b in z.get('productionDeclarationRenames',{}).items()}
assert len(declarationRenames)==len(set(declarationRenames.values()))==3
queries=[declarationRenames.get(n,n) for n in queries]
theorems=[declarationRenames.get(n,n) for n in theorems]
defs=[declarationRenames.get(n,n) for n in defs]
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (28, 28, 436, 371, 65)
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
archive_rel='Tools/projective-residual-image-20261117-2326'
evidence=[p/n for n in ['Dubon Projective Residual Image Assessment 2026-11-17.md', 'SourceDicksonClassification-2294.exit', 'SourceDicksonClassification-2294.log', 'SourceDicksonClassification.lean', 'SourceDicksonCyclicPartition-2294.exit', 'SourceDicksonCyclicPartition-2294.log', 'SourceDicksonCyclicPartition.lean', 'SourceDicksonFieldReconstruction-2294.exit', 'SourceDicksonFieldReconstruction-2294.log', 'SourceDicksonFieldReconstruction.lean', 'SourceDicksonMatrixAlternatives-2311.exit', 'SourceDicksonMatrixAlternatives-2311.log', 'SourceDicksonMatrixAlternatives.lean', 'SourceDicksonNatClassEquation-2294.exit', 'SourceDicksonNatClassEquation-2294.log', 'SourceDicksonNatClassEquation.lean', 'SourceDicksonObjects-2294.exit', 'SourceDicksonObjects-2294.log', 'SourceDicksonObjects.lean', 'SourceDicksonPGLBasic-2294.exit', 'SourceDicksonPGLBasic-2294.log', 'SourceDicksonPGLBasic.lean', 'SourceDicksonPSLBasic-2294.exit', 'SourceDicksonPSLBasic-2294.log', 'SourceDicksonPSLBasic.lean', 'SourceDicksonPSLRecognition-2294.exit', 'SourceDicksonPSLRecognition-2294.log', 'SourceDicksonPSLRecognition.lean', 'SourceDicksonPartitionHelpers-2294.exit', 'SourceDicksonPartitionHelpers-2294.log', 'SourceDicksonPartitionHelpers.lean', 'SourceDicksonPartitionProof-2294.exit', 'SourceDicksonPartitionProof-2294.log', 'SourceDicksonPartitionProof.lean', 'SourceDicksonProjectiveConjugacy-2311.exit', 'SourceDicksonProjectiveConjugacy-2311.log', 'SourceDicksonProjectiveConjugacy.lean', 'SourceDicksonQualifiedNames2322.exit', 'SourceDicksonQualifiedNames2322.lean', 'SourceDicksonQualifiedNames2322.log', 'SourceDicksonRecognitionA5-2294.exit', 'SourceDicksonRecognitionA5-2294.log', 'SourceDicksonRecognitionA5.lean', 'SourceDicksonTameClassification-2294.exit', 'SourceDicksonTameClassification-2294.log', 'SourceDicksonTameClassification.lean', 'SourceDicksonWildClassification-2294.exit', 'SourceDicksonWildClassification-2294.log', 'SourceDicksonWildClassification.lean', 'SourceGammaOneFiniteProjectiveLinearResidual-2321.exit', 'SourceGammaOneFiniteProjectiveLinearResidual-2321.log', 'SourceGammaOneFiniteProjectiveLinearResidual.lean', 'SourceGammaOneProjectiveLinearResidual-2311.exit', 'SourceGammaOneProjectiveLinearResidual-2311.log', 'SourceGammaOneProjectiveLinearResidual.lean', 'SourceGammaOneProjectiveMatrixResidual-2311.exit', 'SourceGammaOneProjectiveMatrixResidual-2311.log', 'SourceGammaOneProjectiveMatrixResidual.lean', 'SourceGammaOneProjectiveResidual-2299.exit', 'SourceGammaOneProjectiveResidual-2299.log', 'SourceGammaOneProjectiveResidual.lean', 'SourceProjectiveFiniteAudit1.exit', 'SourceProjectiveFiniteAudit1.lean', 'SourceProjectiveFiniteAudit1.log', 'SourceProjectiveFiniteDeclarations2321.exit', 'SourceProjectiveFiniteDeclarations2321.lean', 'SourceProjectiveFiniteDeclarations2321.log', 'SourceProjectiveFiniteDependencyAudit1.exit', 'SourceProjectiveFiniteDependencyAudit1.lean', 'SourceProjectiveFiniteDependencyAudit1.log', 'SourceProjectiveLinearAudit2.exit', 'SourceProjectiveLinearAudit2.lean', 'SourceProjectiveLinearAudit2.log', 'SourceProjectiveLinearDeclarations2311.exit', 'SourceProjectiveLinearDeclarations2311.lean', 'SourceProjectiveLinearDeclarations2311.log', 'SourceProjectiveLinearDependencyAudit2.exit', 'SourceProjectiveLinearDependencyAudit2.lean', 'SourceProjectiveLinearDependencyAudit2.log', 'SourceProjectivePerfectLift-2311.exit', 'SourceProjectivePerfectLift-2311.log', 'SourceProjectivePerfectLift.lean', 'SourceProjectiveSL2Lift-2311.exit', 'SourceProjectiveSL2Lift-2311.log', 'SourceProjectiveSL2Lift.lean', 'SourceProjectiveSubfieldBounds-2311.exit', 'SourceProjectiveSubfieldBounds-2311.log', 'SourceProjectiveSubfieldBounds.lean', 'SourceResidualFiniteAmbient-2321.exit', 'SourceResidualFiniteAmbient-2321.log', 'SourceResidualFiniteAmbient.lean', 'SourceResidualFiniteBounds-2321.exit', 'SourceResidualFiniteBounds-2321.log', 'SourceResidualFiniteBounds.lean', 'SourceResidualFiniteDescent-2321.exit', 'SourceResidualFiniteDescent-2321.log', 'SourceResidualFiniteDescent.lean', 'SourceResidualFiniteLinearAlternatives-2321.exit', 'SourceResidualFiniteLinearAlternatives-2321.log', 'SourceResidualFiniteLinearAlternatives.lean', 'SourceResidualLinearAlternatives-2311.exit', 'SourceResidualLinearAlternatives-2311.log', 'SourceResidualLinearAlternatives.lean', 'SourceResidualProjectiveClassification-2294.exit', 'SourceResidualProjectiveClassification-2294.log', 'SourceResidualProjectiveClassification.lean', 'projective-residual-image-promotion-route-2326.json', 'source-projective-28-scratch-summary-2324.json', 'source-projective-finite-audit-config-2321.json', 'source-projective-finite-normalized-1-reuse-review-2324.json', 'source-projective-finite-normalized-1-scratch-receipt.json', 'source-projective-linear-audit-config-2313.json', 'source-projective-linear-normalized-1-reuse-review-2324.json', 'source-projective-linear-normalized-1-scratch-receipt.json', 'source-projective-linear-ownership-reconciliation-2315.json']]
evidence += [p/n for n in ['SourceProjectiveScratchSemantic2327b.lean','SourceProjectiveScratchSemantic2327b.log','SourceProjectiveScratchSemantic2327b.exit','SourceProjectiveScratchSemantic2327.lean','SourceProjectiveScratchSemantic2327.log','SourceProjectiveScratchSemantic2327.exit']]
assert (p/'SourceProjectiveScratchSemantic2327b.exit').read_text().strip()=='0'

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
supplemental_review_path=r/archive_rel/'projective-residual-image-promotion-route-2326.json'

audit = r / "Extension/Dubon2026/Audit.lean"
at = audit.read_text(encoding="utf-8")
for n in queries:
    assert not re.search(r"``" + re.escape(n) + r"(?=[,\s])", at)
tm, dm = "\n]\n\nprivate def publicConstructions", "\n]\n\nprivate def runAudit"
assert at.count(tm) == at.count(dm) == 1
at = at.replace(tm, "".join("\n  ,``" + n for n in theorems) + tm, 1)
at = at.replace(dm, "".join("\n  ," + chr(96)*2 + n for n in defs) + dm, 1)
research_path = r / "Tools/lean-reuse-audit-20261020.json"
reuse_path = r / "Tools/source-projective-residual-image.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt9697"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> automorphy -> original residual large image -> actual projective classification and finite linear subfield bounds.'
discharged = 'For the actual original primitive cusp form of weight at least two and prime p greater than three, the constructed integral/residual arithmetic representation now has the complete Dickson projective alternatives. In the two Lie-type cases, the proof identifies the literal projective matrix subgroup after conjugacy. Native perfection of SL2 removes central scalar ambiguity, giving a literal SL2 lower bound and scalar-GL2 upper bound over the same finite subfield. Both coefficient embeddings and the conjugating matrix descend into one actual finite intermediate field, and both linear bounds descend. The final original-form consumer retains integral origin, literal reduction, fixed-local Hecke characteristic polynomials and inertia, global cyclotomic determinant, maximal Hecke kernel, finite image and oddness. It supplies no representation, image classification, conjugacy or finite-field comparison certificate. The final alternative still explicitly retains cyclic, dihedral, A4, S4, A5 and elementary-abelian-by-cyclic projective images.'
boundary = 'Arithmetic exclusion of the six small-image cases and the required original local deformation/regularity comparison remain open, as do automorphy and literal higher symmetric-power continuation. The finite coefficient field is a constructed extension of the original residue field; no equality of ambient and image fields is asserted. The current source consumers have p greater than three and weight at least two. Acceptance remains 16/20; DUB-17--20 OPEN. The frozen source, full modular domain and all verification criteria are unchanged.'
status = 'The 28-module scratch scope passes 436 public axiom queries, 939 exhaustive theorem checks and all other declaration checks, sixteen linters per module and two declaration-value audits with 81 required edges across the two consumers, with zero diagnostics. Production aggregate, focused audits and sequential foundation/paper verification of the 9,725-module scope are pending.'
route = 'Reuse ImperialCollegeLondon/FLT@478c1013cd29c27d72f57aa8b691fa46083664b3 for the complete proved Dickson closure, omitting admitted statement copies and preserving the Apache-2.0 notices. Reuse native perfect SL2 and Mathlib finite intermediate-field adjunction and matrix maps, retaining subgroup equalities already present inside the upstream argument. The existing primitive_satoTate_of_entire_symmetric_continuation derives purity and boundary nonvanishing from the genuine entire symmetric family; an independent Weil port is only a possible upstream aid. The freshly inspected Ribet irreducibility sources concern weight two and do not discharge the full-weight local conditions. Two strict VALUE audits verify 36 and 45 required dependencies; all default proof limits and diagnostic policies remain unchanged.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Original projective residual image and finite linear bounds (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 9,697-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
corrections = []
count = sum(z['exhaustiveTheorems'] for z in certs)
assert count == 939

docpaths = list(dict.fromkeys(r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]))
for f in docpaths:
    assert "\n\n" in f.read_text(encoding="utf-8")
readmes = [(r.parent / "README.md", "Current Project 83 status ("), (repo / "README.md", "Project 83 has an ")]
for f, prefix in readmes:
    assert sum(line.startswith(prefix) for line in f.read_text(encoding="utf-8").splitlines()) == 1
arch = r / "Dubon Architecture.md"
edge = '  RANKTWO9697["Actual continuous rank-two matrices, oddness, norm-inertia triviality, arithmetic descent, exact integral/residual realization, fixed-local Hecke data and global cyclotomic determinant proved for p greater than three. Remaining association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourceProjectiveResidualImageProductionAudit9725.lean',p/'source-projective-residual-image-9725-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production9725.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/original-rank-two-residual-20261117-2268'
registered = {row['path'] for row in c['files']}
for priorFile in priorArchive.iterdir():
    rel = priorFile.relative_to(r).as_posix()
    if priorFile.is_file() and rel not in registered:
        c['files'].append({'path': rel, 'role': 'Tools'})

reportSource = p / 'Dubon Projective Residual Image Assessment 2026-11-17.md'
assert sha(reportSource) == 'E0FE687B1349242CCF8F85782430B9AC8D6791848700C387A86431535DC22C74'
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
    "productionModules": 9725, "modules": newmods, "queries": queries,
    "theoremRegistrations": theorems, "constructionRegistrations": defs,
    "sourceHashes": {mapping[t.stem]: sha(t) for t, _ in pending}, "scratchCertificates": certs,
    "exactDependency": dependency, "assumptionsDischarged": discharged, "stillOpen": boundary,
    "status": status, "rootPinsChanged": False, "proofLimitsChanged": False,
    "promotionChanges": 'Only scratch imports are qualified to registered production modules. All audited statements, proof bodies and comments remain identical. Three compiler-generated public prime-instance names change under the production module prefix; the exact names were independently compiled and enumerated, and ownership/type/value comparison is mandatory. Actual modular forms and their original arithmetic data are retained; no assumption or completion criterion is weakened.',
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
arch.write_text(arch.read_text(encoding="utf-8").replace(edge,'  RANKTWO9697["Actual original arithmetic integral/residual representation, fixed-local Hecke data and global determinant constructed (DUB-17/18)"] --> PROJECTIVE9725\n  PROJECTIVE9725["Original projective classification, explicit conjugacy and literal SL2/scalar-GL2 bounds over a finite coefficient extension proved. Six small-image exclusions, local regularity and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'),encoding="utf-8")



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Original projective residual image and finite linear bounds - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-projective-residual-image.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub('  logInfo m!".*"\n', '  logInfo m!"SOURCE PROJECTIVE RESIDUAL IMAGE AUDIT PASS: {count} theorems including private/generated declarations. Original projective residual image and finite linear bounds with exact Fourier Frobenius values proved. Remaining association and higher continuation OPEN;16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourceProjectiveResidualImageProductionAudit9725.lean").write_text(out, encoding="utf-8")
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
    target = p / (source.stem + "Production9725.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
(p / "source-projective-residual-image-9725-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 9725, "increment": 28, "queries": 436,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
