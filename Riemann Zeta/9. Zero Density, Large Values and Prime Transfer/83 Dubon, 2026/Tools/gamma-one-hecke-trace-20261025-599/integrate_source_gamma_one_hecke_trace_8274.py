from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 8248
assert d["appliedSourcePrimitiveFiniteH1Realization"]["receipt8248"]["exit"] == 0
assert (p / "paper-verification-8248-console.exit").read_text().strip() == "0"
key = "appliedSourceGammaOneHeckeTrace"
assert key not in d
digests = {'source-gamma-one-hecke-trace-7-scratch-receipt.json': '636683BBCF0384B183C9A6D34E27B01D2C4626196315F09BB916C4145C88C8DD', 'source-gamma-one-hecke-cosets-5-scratch-receipt.json': '1613529C9CBAB0E5553D535E8E5047878665F6CDEFE1CF5D92BB17D9FAE11A45', 'source-gamma-one-hecke-pullback-3-scratch-receipt.json': '12F9D7C6E6CB506406C5D7E342B0F1C81875490FC9BA557E6DBA26BF29AA641B', 'source-h1-trace-base-change-3-scratch-receipt.json': '974069BB8FB44C3BE2A0E2977AD160007EEA94199C783D4122D7890B8E125A4D', 'source-gamma-one-cover-trace-base-change-4-scratch-receipt.json': 'C87C90F4B8429300BCAAB5233A3919E08A321969E004AA2AF67172A8035FA29F', 'source-h1-trace-tower-4-scratch-receipt.json': '155CB8353C187305C00C9AE6A7321C1506786249C10B3A0874737FF137C25718'}

for name, digest in digests.items():
    assert sha(p / name) == digest
certs = [json.loads((p / name).read_text(encoding="utf-8")) for name in digests]
mods = [m for z in certs for m in z["modules"]]
queries = [q for z in certs for q in z["queries"]]
theorems = [q for z in certs for q in z["theoremRegistrations"]]
defs = [q for z in certs for q in z["constructionRegistrations"]]
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (26, 26, 77, 55, 22)
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
archive_rel='Tools/gamma-one-hecke-trace-20261025-599'
evidence=[p/'gamma-one-hecke-trace-promotion-route-599.json']
evidence += [p/name for name in ['SourceGammaOneCoverTraceBaseChangeAudit4.exit', 'SourceGammaOneCoverTraceBaseChangeAudit4.lean', 'SourceGammaOneCoverTraceBaseChangeAudit4.log', 'SourceGammaOneCoverTraceBaseChangeDependencyAudit4.exit', 'SourceGammaOneCoverTraceBaseChangeDependencyAudit4.lean', 'SourceGammaOneCoverTraceBaseChangeDependencyAudit4.log', 'SourceGammaOneHeckeCosetsAudit5.exit', 'SourceGammaOneHeckeCosetsAudit5.lean', 'SourceGammaOneHeckeCosetsAudit5.log', 'SourceGammaOneHeckeCosetsDependencyAudit5.exit', 'SourceGammaOneHeckeCosetsDependencyAudit5.lean', 'SourceGammaOneHeckeCosetsDependencyAudit5.log', 'SourceGammaOneHeckePullbackAudit3.exit', 'SourceGammaOneHeckePullbackAudit3.lean', 'SourceGammaOneHeckePullbackAudit3.log', 'SourceGammaOneHeckePullbackDependencyAudit3.exit', 'SourceGammaOneHeckePullbackDependencyAudit3.lean', 'SourceGammaOneHeckePullbackDependencyAudit3.log', 'SourceGammaOneHeckeTraceAudit7.exit', 'SourceGammaOneHeckeTraceAudit7.lean', 'SourceGammaOneHeckeTraceAudit7.log', 'SourceGammaOneHeckeTraceDependencyAudit7.exit', 'SourceGammaOneHeckeTraceDependencyAudit7.lean', 'SourceGammaOneHeckeTraceDependencyAudit7.log', 'SourceH1TraceBaseChangeAudit3.exit', 'SourceH1TraceBaseChangeAudit3.lean', 'SourceH1TraceBaseChangeAudit3.log', 'SourceH1TraceBaseChangeDependencyAudit3.exit', 'SourceH1TraceBaseChangeDependencyAudit3.lean', 'SourceH1TraceBaseChangeDependencyAudit3.log', 'SourceH1TraceTowerAudit4.exit', 'SourceH1TraceTowerAudit4.lean', 'SourceH1TraceTowerAudit4.log', 'SourceH1TraceTowerDependencyAudit4.exit', 'SourceH1TraceTowerDependencyAudit4.lean', 'SourceH1TraceTowerDependencyAudit4.log', 'gamma1-cohomology-hecke-compatibility-route-595.json', 'gamma1-hecke-comparison-route-592.json', 'gamma1-hecke-square-route-594.json', 'gamma1-hecke-transfer-group-hypotheses-route-597.json', 'gamma1-transfer-base-change-route-596.json', 'gamma1-transfer-trace-composition-route-598.json', 'prepare_gamma_one_cover_trace_base_change_audit_597.py', 'prepare_gamma_one_hecke_cosets_audit_594.py', 'prepare_gamma_one_hecke_pullback_audit_595.py', 'prepare_gamma_one_hecke_trace_audit_592.py', 'prepare_h1_trace_base_change_audit_596.py', 'prepare_h1_trace_tower_audit_598.py', 'record_gamma_one_cover_trace_base_change_597.py', 'record_gamma_one_hecke_cosets_594.py', 'record_gamma_one_hecke_pullback_595.py', 'record_gamma_one_hecke_trace_592.py', 'record_h1_trace_base_change_596.py', 'record_h1_trace_tower_598.py', 'source-gamma-one-cover-trace-base-change-4-audit-config.json', 'source-gamma-one-cover-trace-base-change-4-scratch-receipt.json', 'source-gamma-one-hecke-cosets-5-audit-config.json', 'source-gamma-one-hecke-cosets-5-scratch-receipt.json', 'source-gamma-one-hecke-pullback-3-audit-config.json', 'source-gamma-one-hecke-pullback-3-scratch-receipt.json', 'source-gamma-one-hecke-trace-7-audit-config.json', 'source-gamma-one-hecke-trace-7-scratch-receipt.json', 'source-h1-trace-base-change-3-audit-config.json', 'source-h1-trace-base-change-3-scratch-receipt.json', 'source-h1-trace-tower-4-audit-config.json', 'source-h1-trace-tower-4-scratch-receipt.json']]
for folder in ['shapiro-h1-trace-592-before-explicit-map','shapiro-h1-trace-592-before-direct-congruence']:
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
supplemental_review_path=r/archive_rel/'gamma-one-hecke-trace-promotion-route-599.json'

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
reuse_path = r / "Tools/source-gamma-one-hecke-trace.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt8248"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero Galois association -> geometric Gamma1 realization -> original surjective-transfer Hecke compatibility -> exact native trace, correspondence square, group base change and trace composition'
discharged = 'The actual finite-index Gamma1 H1 transfer is identified with the literal native finite-coset trace, using the native counit formula and the original Shapiro cocycle comparison. Its surjectivity therefore holds for that literal trace. The actual Gamma1 constant-coefficient Hecke correspondence is defined by the original integral diagonal conjugation and full finite coset sum. Coprime principal-level reduction supplies the exact Gamma1/raised-level coset bijection, the literal cover commutes with Hecke conjugation, and the corresponding representatives have the exact conjugated transitions. Restriction of the original binary H1 to the genuine constant-coefficient Gamma1 H1 commutes with the original Hecke operator, retaining the homogeneous matrix coefficient action. Native H1 trace base change is derived by pulling back actual coinduced functions, reindexing the complete coefficient trace and applying the original Shapiro restriction/evaluation theorem. The concrete Gamma1 image has proved congruences and principal-level containment; these prove good-prime conjugation preservation, identify the exact intersection subgroup, and discharge coset surjectivity in the actual Hecke base-change application. Finally, actual nested coinduced functions form a proved isomorphism. Native quotient-product reindexing proves coefficient-trace composition, and the existing Shapiro comparison and coefficient naturality descend it to the full literal H1 trace. No trace formula, coset-surjectivity, Shapiro-composition, trace-transitivity or restriction/Hecke compatibility premise remains in these consumers.'
boundary = 'The surjective-transfer Hecke identity still requires combining the proved base-change and trace-composition identities with the original coefficient action and exact subgroup reindexings. Restriction compatibility alone does not establish this transfer identity. Arithmetic geometric and diamond compatibility, geometric Galois realization of the finite characters, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain required. No characteristic-zero character lift or deformation point is inferred from finite characters. 16/20; DUB-17--20 OPEN.'
status = 'The actual Gamma1 Hecke and native trace comparison chain passes 111 exhaustive scratch checks and 77 explicit axiom queries across 26 modules, with sixteen linters per module and zero diagnostics. Six declaration-value audits verify 123 required dependencies. Production aggregate, focused audit and sequential foundation/paper verification of the 8,274-module scope are pending.'
route = 'Reuse the original coinduced coset trace, native counit, Shapiro restriction/evaluation and cocycle homotopy, existing level raising and Hecke conjugation, full SL2 reduction and its Chinese-remainder equivalence, chosen-representative coboundary comparison, native subgroup quotient maps and subgroupOf equivalence. Direct coefficient-function pullback and native quotient-product reindexing avoid new resolutions, a general Mackey development and new strong approximation. The duplicate abstract transfer-formula module remains deferred. The renewed external search and its characteristic-zero Gamma1 character boundary remain unchanged; no new external import or pin change.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Actual Gamma1 Hecke and native trace comparisons (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 8,248-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
corrections = []
count = sum(z['exhaustiveTheorems'] for z in certs)
assert count == 111

docpaths = list(dict.fromkeys(r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]))
for f in docpaths:
    assert "\n\n" in f.read_text(encoding="utf-8")
readmes = [(r.parent / "README.md", "Current Project 83 status ("), (repo / "README.md", "Project 83 has an ")]
for f, prefix in readmes:
    assert sum(line.startswith(prefix) for line in f.read_text(encoding="utf-8").splitlines()) == 1
arch = r / "Dubon Architecture.md"
edge = '  PRIMITIVEFINITEH18248["Compatible original finite H1 and permutation Hecke characters with a canonical surjection, congruence-stabilizer comparison and exact constant-coefficient Gamma1 realization proved; geometric Galois realization, adic association, local/image/regularity and automorphy OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourceGammaOneHeckeTraceProductionAudit8274.lean',p/'source-gamma-one-hecke-trace-8274-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production8274.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/primitive-finite-gamma-one-h1-20261025-593'
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
reuse['dependencyRouteAssessment'] = dict(path=supplemental_review_path.relative_to(r).as_posix(),sha256=sha(supplemental_review_path))
reuse['proofEvidenceArchive'] = dict(manifest=archive_target.relative_to(r).as_posix(),sha256=sha(archive_target),externalLocalBuild=False,externalImport=False)
reuse_path.write_text(json.dumps(reuse, indent=2) + "\n", encoding="utf-8")
c["files"].append({"path": reuse_path.relative_to(r).as_posix(), "role": "Tools"})
cp.write_text(json.dumps(c, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
d[key] = {"recordedUTC": datetime.now(timezone.utc).isoformat(), "date": dateLabel,
    "productionModules": 8274, "modules": newmods, "queries": queries,
    "theoremRegistrations": theorems, "constructionRegistrations": defs,
    "sourceHashes": {mapping[t.stem]: sha(t) for t, _ in pending}, "scratchCertificates": certs,
    "exactDependency": dependency, "assumptionsDischarged": discharged, "stillOpen": boundary,
    "status": status, "rootPinsChanged": False, "proofLimitsChanged": False,
    "promotionChanges": 'Only scratch imports are qualified. Every mathematical statement, proof body and module comment is preserved. The original Gamma1 cover, Hecke correspondences, binary coefficients, native cohomology, literal finite traces and subgroup reindexings retain their definitions. No source contract is weakened.',
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
arch.write_text(arch.read_text(encoding='utf-8').replace(edge,'  PRIMITIVEFINITEH18248["Compatible original finite H1 and permutation Hecke characters with a canonical surjection and exact constant-coefficient Gamma1 realization (DUB-17/18)"] --> GAMMAONEHECKETRACE8274\n  GAMMAONEHECKETRACE8274["Literal native Gamma1 trace, Hecke restriction, actual Hecke base change and trace composition proved; surjective-transfer assembly, arithmetic Galois realization and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'),encoding='utf-8')



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Actual Gamma1 Hecke and native trace comparisons - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-gamma-one-hecke-trace.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub(r'  logInfo m!".*"\n',
    '  logInfo m!"SOURCE GAMMA ONE HECKE TRACE AUDIT PASS: {count} theorems including private/generated declarations. The literal native Gamma1 trace, original Hecke restriction compatibility, actual Hecke base change and trace composition are proved. Surjective-transfer assembly, arithmetic Galois realization, all-weight association and higher continuation remain open; 16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourceGammaOneHeckeTraceProductionAudit8274.lean").write_text(out, encoding="utf-8")
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
    target = p / (source.stem + "Production8274.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
(p / "source-gamma-one-hecke-trace-8274-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 8274, "increment": 26, "queries": 77,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
