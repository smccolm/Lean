from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 8193
assert d["appliedSourcePrimitiveResidualAssociation"]["receipt8193"]["exit"] == 0
assert (p / "paper-verification-8193-console.exit").read_text().strip() == "0"
key = "appliedSourcePrimitiveWittDeformation"
assert key not in d
digests = {'source-primitive-residual-determinant-3-scratch-receipt.json': '3A144622C8E86F3CEC3CDDB30007F3ED84B4A09BE5568F8C0460980E6EE947C2', 'source-primitive-residual-oddness-2-scratch-receipt.json': 'BCA9D4B759D99519AEF314F0A3CD952713308E48D43F8AC19C9DBE3910657391', 'source-primitive-finite-residual-4-scratch-receipt.json': '522BEB44D05905C7E81529F223EEFCD9F2A84B01BD3B5CED15790B94C9CD434A', 'source-primitive-witt-framed-4-scratch-receipt.json': 'DF5519482C8779B0EC2C0B4F456148F3A826099D58E4319E185E853817FCBAD0', 'source-primitive-witt-fixed-7-scratch-receipt.json': '3FFE0D41628C7D61F16D1D893E5C84AAD076E1316941592485E3C59C3D02B1BE'}

for name, digest in digests.items():
    assert sha(p / name) == digest
certs = [json.loads((p / name).read_text(encoding="utf-8")) for name in digests]
mods = [m for z in certs for m in z["modules"]]
queries = [q for z in certs for q in z["queries"]]
theorems = [q for z in certs for q in z["theoremRegistrations"]]
defs = [q for z in certs for q in z["constructionRegistrations"]]
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (20, 20, 36, 29, 7)
omitted = []
assert not set(mods).intersection(c["productionModules"])
mapping = {m: "Dubon2026." + m for m in c["productionModules"] + mods}
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
        assert f.with_suffix(".exit").read_text().strip() == "0" and f.with_suffix(".log").stat().st_size == 0
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
archive_rel='Tools/primitive-witt-20261025-581'
evidence=[p/'primitive-witt-deformation-promotion-route-581.json']

evidence += [p/name for name in digests]
evidence += [p/name for name in ['SourcePrimitiveFiniteResidualAudit4.exit', 'SourcePrimitiveFiniteResidualAudit4.lean', 'SourcePrimitiveFiniteResidualAudit4.log', 'SourcePrimitiveFiniteResidualDependencyAudit4.exit', 'SourcePrimitiveFiniteResidualDependencyAudit4.lean', 'SourcePrimitiveFiniteResidualDependencyAudit4.log', 'SourcePrimitiveResidualDeterminantAudit3.exit', 'SourcePrimitiveResidualDeterminantAudit3.lean', 'SourcePrimitiveResidualDeterminantAudit3.log', 'SourcePrimitiveResidualDeterminantDependencyAudit3.exit', 'SourcePrimitiveResidualDeterminantDependencyAudit3.lean', 'SourcePrimitiveResidualDeterminantDependencyAudit3.log', 'SourcePrimitiveResidualDeterminantDependencyAudit3b.exit', 'SourcePrimitiveResidualDeterminantDependencyAudit3b.lean', 'SourcePrimitiveResidualDeterminantDependencyAudit3b.log', 'SourcePrimitiveResidualOddnessAudit2.exit', 'SourcePrimitiveResidualOddnessAudit2.lean', 'SourcePrimitiveResidualOddnessAudit2.log', 'SourcePrimitiveResidualOddnessDependencyAudit2.exit', 'SourcePrimitiveResidualOddnessDependencyAudit2.lean', 'SourcePrimitiveResidualOddnessDependencyAudit2.log', 'SourcePrimitiveResidualOddnessDependencyAudit2b.exit', 'SourcePrimitiveResidualOddnessDependencyAudit2b.lean', 'SourcePrimitiveResidualOddnessDependencyAudit2b.log', 'SourcePrimitiveWittFixedAudit7.exit', 'SourcePrimitiveWittFixedAudit7.lean', 'SourcePrimitiveWittFixedAudit7.log', 'SourcePrimitiveWittFixedDependencyAudit7.exit', 'SourcePrimitiveWittFixedDependencyAudit7.lean', 'SourcePrimitiveWittFixedDependencyAudit7.log', 'SourcePrimitiveWittFramedAudit4.exit', 'SourcePrimitiveWittFramedAudit4.lean', 'SourcePrimitiveWittFramedAudit4.log', 'SourcePrimitiveWittFramedDependencyAudit4.exit', 'SourcePrimitiveWittFramedDependencyAudit4.lean', 'SourcePrimitiveWittFramedDependencyAudit4.log', 'SourcePrimitiveWittFramedDependencyAudit4b.exit', 'SourcePrimitiveWittFramedDependencyAudit4b.lean', 'SourcePrimitiveWittFramedDependencyAudit4b.log', 'prepare_primitive_finite_residual_audit_575.py', 'prepare_primitive_residual_determinant_audit_572.py', 'prepare_primitive_residual_oddness_audit_574.py', 'prepare_primitive_witt_fixed_audit_580.py', 'prepare_primitive_witt_framed_audit_577.py', 'primitive-finite-residual-route-575.json', 'primitive-residual-determinant-route-572.json', 'primitive-residual-determinant-route-572b.json', 'primitive-residual-determinant-serialization-successor-572b.json', 'primitive-residual-oddness-route-574.json', 'primitive-residual-oddness-route-574b.json', 'primitive-residual-oddness-serialization-successor-574b.json', 'primitive-witt-fixed-route-580.json', 'primitive-witt-framed-route-577.json', 'primitive-witt-framed-route-577b.json', 'primitive-witt-framed-serialization-successor-577b.json', 'record_primitive_finite_residual_575.py', 'record_primitive_residual_determinant_572b.py', 'record_primitive_residual_oddness_574b.py', 'record_primitive_residual_oddness_574c.py', 'record_primitive_witt_fixed_580.py', 'record_primitive_witt_framed_577.py', 'record_primitive_witt_framed_577b.py', 'source-primitive-finite-residual-4-audit-config.json', 'source-primitive-residual-determinant-3-audit-config.json', 'source-primitive-residual-oddness-2-audit-config.json', 'source-primitive-witt-fixed-7-audit-config.json', 'source-primitive-witt-framed-4-audit-config.json']]
for folder in ['finite-residual-575-before-abstract-descent','witt-framed-577-before-named-conclusion']:
    evidence += sorted((p/folder).iterdir())
for cert in certs:
    evidence.append(Path(cert['reuseReview']))

for cert in certs:
    for field in ['log','dependencyAuditLog']:
        f=Path(cert[field]); evidence.extend([f,f.with_suffix('.lean'),f.with_suffix('.exit')])
archive=[]
for source in dict.fromkeys(evidence):
    assert source.exists(),source
    target=r/archive_rel/(source.parent.name if source.parent != p else '')/(source.name+('.txt' if source.suffix=='.lean' else ''))
    assert not target.exists(),target
    refresh_pending.append((target,source.read_bytes(),'Tools'))
    archive.append(dict(source=str(source),path=target.relative_to(r).as_posix(),sha256=sha(source)))
archive_target=r/archive_rel/'archive-manifest.json'
assert not archive_target.exists()
refresh_pending.append((archive_target,(json.dumps(dict(files=archive),indent=2)+'\n').encode(),'Tools'))
supplemental_review_path=r/archive_rel/'primitive-witt-deformation-promotion-route-581.json'

audit = r / "Extension/Dubon2026/Audit.lean"
at = audit.read_text(encoding="utf-8")
for n in queries:
    assert not re.search(r"``" + re.escape(n) + r"(?=[,\s])", at)
tm, dm = "\n]\n\nprivate def publicConstructions", "\n]\n\nprivate def runAudit"
assert at.count(tm) == at.count(dm) == 1
at = at.replace(tm, "".join("\n  ,``" + n for n in theorems) + tm, 1)
at = at.replace(dm, "," + "".join("\n  ``" + n + ("," if i + 1 < len(defs) else "")
                                 for i, n in enumerate(defs)) + dm, 1)
research_path = r / "Tools/lean-reuse-audit-20261020.json"
reuse_path = r / "Tools/source-primitive-witt-deformation.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt8193"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> actual original all-weight residual deformation problem -> global cyclotomic determinant, real oddness, finite coefficients and genuine p-adic fixed-determinant quotient'
discharged = 'The original primitive form in every weight at least two and every prescribed prime supplies the same original-support residual representation over a constructed finite field. Its global determinant is the cyclotomic power k-1; its determinant at actual complex conjugation is minus one. Original Fourier reductions, good-prime determinants and inertia remain unchanged. The native Witt coefficient ring has precisely this finite residue field. The existing actual framed and fixed-determinant rings are Noetherian and complete and their universal matrices reduce to that same representation. Every p-power root lies in the original arithmetic extension by support-power inclusion, so the native p-adic cyclotomic character has the actual root action. Its Witt scalar image reduces to the original finite character and supplies the genuine weight determinant of the fixed-determinant quotient. No global residual determinant, oddness, finite coefficient, Witt residue, prime-power root or determinant compatibility assumption remains.'
boundary = 'A characteristic-zero coefficient ring does not provide a characteristic-zero point of the deformation ring. Original all-weight adic association, required local, image and regularity properties, arithmetic automorphy and literal higher symmetric-power continuation remain required. 16/20; DUB-17--20 OPEN.'
status = 'The actual original-form residual determinant and deformation chain passes 62 exhaustive scratch checks and 36 explicit axiom queries across 20 modules, with sixteen linters per module and zero diagnostics. Five declaration-value audits verify 63 required dependencies. Failed serialization checks and fresh successors, plus stopped unaudited elaboration attempts and unchanged-conclusion refinements, are preserved. Production aggregate, focused audit and sequential foundation/paper verification of the 8,213-module scope are pending.'
route = 'Reuse the proved original residual association and character density, native finite algebraic adjunction and coefficient mapping, SourceWittLift and native Witt DVR/completeness, and the existing actual framed and fixed-determinant constructions. Native WittVector.fromPadicInt and cyclotomicCharacter avoid new scalar-lift and character infrastructure; existing support-power inclusion supplies all required roots. The renewed primary-source review finds overlapping weight-two code and a later Hodge-Tate candidate, without a ready all-weight association proof. No external import, root pin, proof-limit change or incidental generalization.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Actual original-form cyclotomic determinant and deformation rings (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 8,193-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
corrections = []
count = sum(z['exhaustiveTheorems'] for z in certs)
assert count == 62

docpaths = list(dict.fromkeys(r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]))
for f in docpaths:
    assert "\n\n" in f.read_text(encoding="utf-8")
readmes = [(r.parent / "README.md", "Current Project 83 status ("), (repo / "README.md", "Project 83 has an ")]
for f, prefix in readmes:
    assert sum(line.startswith(prefix) for line in f.read_text(encoding="utf-8").splitlines()) == 1
arch = r / "Dubon Architecture.md"
edge = '  PRIMITIVERESIDUAL8193["All-weight original-support residual association: coefficient completion, norm-local comparison, arithmetic descent and parabolic closure proved; global determinant, adic realization, local/image properties and automorphy OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourcePrimitiveWittDeformationProductionAudit8213.lean',p/'source-primitive-witt-deformation-8213-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production8213.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/primitive-residual-20261025-573'
registered = {row['path'] for row in c['files']}
for priorFile in priorArchive.iterdir():
    rel = priorFile.relative_to(r).as_posix()
    if priorFile.is_file() and rel not in registered:
        c['files'].append({'path': rel, 'role': 'Tools'})

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
reuse['additionalCurrentSearch'] = dict(path=supplemental_review_path.relative_to(r).as_posix(),sha256=sha(supplemental_review_path))
reuse['renewedSourceArchive'] = dict(manifest=archive_target.relative_to(r).as_posix(),sha256=sha(archive_target),externalLocalBuild=False,externalImport=False)
reuse_path.write_text(json.dumps(reuse, indent=2) + "\n", encoding="utf-8")
c["files"].append({"path": reuse_path.relative_to(r).as_posix(), "role": "Tools"})
cp.write_text(json.dumps(c, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
d[key] = {"recordedUTC": datetime.now(timezone.utc).isoformat(), "date": dateLabel,
    "productionModules": 8213, "modules": newmods, "queries": queries,
    "theoremRegistrations": theorems, "constructionRegistrations": defs,
    "sourceHashes": {mapping[t.stem]: sha(t) for t, _ in pending}, "scratchCertificates": certs,
    "exactDependency": dependency, "assumptionsDischarged": discharged, "stillOpen": boundary,
    "status": status, "rootPinsChanged": False, "proofLimitsChanged": False,
    "promotionChanges": 'Only scratch imports are qualified. Every mathematical statement, proof body and module comment is preserved. The original primitive cusp form, Fourier coefficients, actual local fields, arithmetic support, parabolic cohomology and weight twist retain their definitions. No source contract is weakened.',
    "omittedScratchTheorems": omitted,
    "existingReuseTheorems": [],
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
arch.write_text(arch.read_text(encoding='utf-8').replace(edge, '  PRIMITIVERESIDUAL8193["All-weight original-support residual association with original Fourier reductions and inertia (DUB-17/18)"] --> PRIMITIVEWITT8213\n  PRIMITIVEWITT8213["Global cyclotomic determinant, real oddness, finite residue field and actual complete Witt framed/fixed-determinant rings proved; original adic point, local/image/regularity and automorphy OPEN (DUB-17/18)"] --> CMARITH4538'),encoding='utf-8')



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Actual original-form cyclotomic determinant and deformation rings - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-primitive-witt-deformation.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub(r'  logInfo m!".*"\n',
    '  logInfo m!"SOURCE PRIMITIVE WITT DEFORMATION AUDIT PASS: {count} theorems including private/generated declarations. The original all-weight form supplies its finite-field residual representation with global cyclotomic determinant and real oddness, together with actual complete framed and genuine cyclotomic fixed-determinant rings over Witt coefficients. Original adic specialization, local/image/regularity properties, automorphy and literal higher continuation remain open; 16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourcePrimitiveWittDeformationProductionAudit8213.lean").write_text(out, encoding="utf-8")
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
    target = p / (source.stem + "Production8213.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
(p / "source-primitive-witt-deformation-8213-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 8213, "increment": 20, "queries": 36,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
