from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 8274
assert d["appliedSourceGammaOneHeckeTrace"]["receipt8274"]["exit"] == 0
assert (p / "paper-verification-8274-console.exit").read_text().strip() == "0"
assert (r/'Tools/gamma-one-hecke-trace-20261025-599/canonical-evidence-8274.json').exists()
key = "appliedSourcePrimitiveGammaOneHeckeRealization"
assert key not in d
digests = {'source-gamma-one-binary-trace-2-scratch-receipt.json': 'B331C5AAAE819979A78B66FC378A14D6E5C210511A55767DD6E9FC1C0821C8D1', 'source-gamma-one-hecke-upper-image-1-scratch-receipt.json': '79962903C2D157BCE54001FC5F26EB61AD1260A3AB3D463B815CFAF8ACDE5485', 'source-gamma-one-subgroup-h1-map-1-scratch-receipt.json': '2A5CCD33B000E4042205791E97CB5FA7A314F226FD1FEB2485794E1978C0EC84', 'source-gamma-one-native-hecke-comparison-2-scratch-receipt.json': 'F56DC4C091DBF9D2EAB5062E447579F49FF7D7E84602C5C7760CE3F97D318F64', 'source-gamma-one-transfer-hecke-5-scratch-receipt.json': 'FF1D68B10A5EC405DCA39498E1EAEF34E2340383062DB2CB9830F867853DCF5A', 'source-primitive-gamma-one-character-5b-scratch-receipt.json': '554371BFDBEFC55035DE31363B405A0C89588A2BA096CF5030F69D7B07EDEA3F'}

for name, digest in digests.items():
    assert sha(p / name) == digest
certs = [json.loads((p / name).read_text(encoding="utf-8")) for name in digests]
mods = [m for z in certs for m in z["modules"]]
queries = [q for z in certs for q in z["queries"]]
theorems = [q for z in certs for q in z["theoremRegistrations"]]
defs = [q for z in certs for q in z["constructionRegistrations"]]
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (16, 16, 41, 30, 11)
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
archive_rel='Tools/primitive-gamma-one-hecke-20261026-618'
evidence=[p/'primitive-gamma-one-hecke-promotion-route-618.json']
evidence += [p/name for name in ['SourceGammaOneBinaryTraceAudit2.exit', 'SourceGammaOneBinaryTraceAudit2.lean', 'SourceGammaOneBinaryTraceAudit2.log', 'SourceGammaOneBinaryTraceDependencyAudit2.exit', 'SourceGammaOneBinaryTraceDependencyAudit2.lean', 'SourceGammaOneBinaryTraceDependencyAudit2.log', 'SourceGammaOneHeckeUpperImageAudit1.exit', 'SourceGammaOneHeckeUpperImageAudit1.lean', 'SourceGammaOneHeckeUpperImageAudit1.log', 'SourceGammaOneHeckeUpperImageDependencyAudit1.exit', 'SourceGammaOneHeckeUpperImageDependencyAudit1.lean', 'SourceGammaOneHeckeUpperImageDependencyAudit1.log', 'SourceGammaOneNativeHeckeComparisonAudit2.exit', 'SourceGammaOneNativeHeckeComparisonAudit2.lean', 'SourceGammaOneNativeHeckeComparisonAudit2.log', 'SourceGammaOneNativeHeckeComparisonDependencyAudit2.exit', 'SourceGammaOneNativeHeckeComparisonDependencyAudit2.lean', 'SourceGammaOneNativeHeckeComparisonDependencyAudit2.log', 'SourceGammaOneSubgroupH1MapAudit1.exit', 'SourceGammaOneSubgroupH1MapAudit1.lean', 'SourceGammaOneSubgroupH1MapAudit1.log', 'SourceGammaOneSubgroupH1MapDependencyAudit1.exit', 'SourceGammaOneSubgroupH1MapDependencyAudit1.lean', 'SourceGammaOneSubgroupH1MapDependencyAudit1.log', 'SourceGammaOneTransferHeckeAudit5.exit', 'SourceGammaOneTransferHeckeAudit5.lean', 'SourceGammaOneTransferHeckeAudit5.log', 'SourceGammaOneTransferHeckeDependencyAudit5.exit', 'SourceGammaOneTransferHeckeDependencyAudit5.lean', 'SourceGammaOneTransferHeckeDependencyAudit5.log', 'SourcePrimitiveGammaOneCharacterAudit5.exit', 'SourcePrimitiveGammaOneCharacterAudit5.lean', 'SourcePrimitiveGammaOneCharacterAudit5.log', 'SourcePrimitiveGammaOneCharacterAudit5b.exit', 'SourcePrimitiveGammaOneCharacterAudit5b.lean', 'SourcePrimitiveGammaOneCharacterAudit5b.log', 'SourcePrimitiveGammaOneCharacterDependencyAudit5.lean', 'SourcePrimitiveGammaOneCharacterDependencyAudit5b.exit', 'SourcePrimitiveGammaOneCharacterDependencyAudit5b.lean', 'SourcePrimitiveGammaOneCharacterDependencyAudit5b.log', 'consumers604.txt', 'consumers611.txt', 'gamma1-actual-transfer-hecke-route-611.json', 'gamma1-binary-hecke-transfer-reduction-route-600.json', 'gamma1-finite-operator-character-route-612.json', 'gamma1-hecke-trace-subgroup-reindex-route-601.json', 'gamma1-intersection-606-before-nested-subgroup-identification.txt', 'gamma1-intersection-trace-exchange-route-606.json', 'gamma1-native-hecke-comparison-route-605.json', 'gamma1-native-hecke-pullback-square-route-603.json', 'gamma1-original-finite-character-route-617.json', 'gamma1-original-finite-character-route-617b.json', 'gamma1-subgroup-h1-transfer-identification-route-602.json', 'gamma1-upper-trace-reindex-route-604.json', 'modules604.json', 'modules611.json', 'prepare_gamma_one_binary_trace_audit_600.py', 'prepare_gamma_one_hecke_upper_image_audit_601.py', 'prepare_gamma_one_native_hecke_comparison_audit_605.py', 'prepare_gamma_one_subgroup_h1_map_audit_602.py', 'prepare_gamma_one_transfer_hecke_audit_611.py', 'prepare_primitive_gamma_one_character_audit_617.py', 'prepare_primitive_gamma_one_character_audit_617b.py', 'record604.py', 'record611.py', 'record_gamma_one_binary_trace_600.py', 'record_gamma_one_hecke_upper_image_601.py', 'record_gamma_one_native_hecke_comparison_605.py', 'record_gamma_one_subgroup_h1_map_602.py', 'record_gamma_one_transfer_hecke_611.py', 'record_primitive_gamma_one_character_617.py', 'record_primitive_gamma_one_character_617b.py', 'registrations604.json', 'registrations611.json', 'section604.txt', 'section611.txt', 'source-gamma-one-binary-trace-2-audit-config.json', 'source-gamma-one-binary-trace-2-scratch-receipt.json', 'source-gamma-one-hecke-upper-image-1-audit-config.json', 'source-gamma-one-hecke-upper-image-1-scratch-receipt.json', 'source-gamma-one-native-hecke-comparison-2-audit-config.json', 'source-gamma-one-native-hecke-comparison-2-scratch-receipt.json', 'source-gamma-one-subgroup-h1-map-1-audit-config.json', 'source-gamma-one-subgroup-h1-map-1-scratch-receipt.json', 'source-gamma-one-transfer-hecke-5-audit-config.json', 'source-gamma-one-transfer-hecke-5-scratch-receipt.json', 'source-primitive-gamma-one-character-5-audit-config.json', 'source-primitive-gamma-one-character-5b-audit-config.json', 'source-primitive-gamma-one-character-5b-scratch-receipt.json', 'status604.txt', 'status611.txt']]
for folder in ['gamma1-character-617-before-unused-operator-instance', 'gamma1-hecke-pullback-603-before-abstract-composition-square', 'gamma1-hecke-pullback-603-before-group-ext', 'gamma1-hecke-pullback-603-before-linear-projections', 'gamma1-operator-descent-613-before-explicit-types', 'gamma1-subgroup-h1-602-before-abstract-iso-comparison', 'gamma1-subgroup-h1-602-before-explicit-map-composition', 'gamma1-subgroup-h1-602-before-iso-hom-rewrites', 'gamma1-subgroup-h1-602-before-native-coefficient-form', 'h1-trace-coefficient-600-before-explicit-composition']:
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
supplemental_review_path=r/archive_rel/'primitive-gamma-one-hecke-promotion-route-618.json'

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
reuse_path = r / "Tools/source-primitive-gamma-one-hecke-realization.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt8274"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero Galois association -> arithmetic Gamma1 geometric realization -> actual surjective-transfer Hecke compatibility and original finite Fourier-valued Gamma1 characters'
discharged = 'The already constructed surjective constant-coefficient Gamma1 H1 transfer now intertwines the actual full original binary Hecke operators at every prime coprime to level times coefficient modulus, retaining the homogeneous matrix coefficient action. Native trace base change with the original coefficient morphism, the exact upper-subgroup isomorphism, the native H1 pullback square and upper-trace reindexing are proved. Applying the existing trace tower through the same actual intersection proves trace exchange; composing these identities and the original literal-transfer formula discharges the full surjective-transfer compatibility. The same actual transfer and existing additive word intertwiner then force every Gamma1 operator relation to hold in the original finite tensor-operator image. Native ring-map descent constructs its canonical comparison. For every original primitive form of weight at least two and every prescribed prime greater than three, the original local embedding and compatible adic character supply characters on the actual finite Gamma1 H1 operator rings at all positive prime-power precisions. Whole-word pullback and the exact original Fourier values at primes away from level and modulus are derived. Native congruence-group finite generation and the existing finite H1 theorem prove these actual operator rings finite. No trace, subgroup, coefficient-action, operator-relation or character-existence premise remains in these consumers.'
boundary = 'Arithmetic geometric and diamond compatibility, geometric Galois realization of the finite characters, original all-weight characteristic-zero association, required local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain required. The new operator generators explicitly omit primes dividing level or modulus; surjectivity onto the entire original Hecke algebra is not asserted. No characteristic-zero character lift or deformation point is inferred from finite characters. 16/20; DUB-17--20 OPEN.'
status = 'The actual Gamma1 transfer and original-form finite-character chain passes 110 exhaustive scratch checks and 41 explicit axiom queries across 16 modules, with sixteen linters per module and zero diagnostics. Six declaration-value audits verify 78 required dependencies. Production aggregate, focused audit and sequential foundation/paper verification of the 8,290-module scope are pending.'
route = 'Reuse the existing native trace tower, cohomology reindexing, coefficient trace naturality, exact congruence subgroup identities and literal original transfer. Apply the proved additive word intertwiner, exact integral reduction kernel, finite operator-character descent, original Fourier character and prescribed-prime completion. Existing finite group-cohomology and the homogeneous monomial basis prove finiteness. Small native map projections and explicit ring objects avoid elaboration timeouts at unchanged limits. The exhaustive linter removed an unnecessary nonzero-modulus binder from the operator definitions; all failed evidence is preserved. No general Mackey development, new word induction, arbitrary eigenvector lift or substitute Hecke operator is used. The renewed external search and its characteristic-zero Gamma1 character boundary remain unchanged; no new external import or pin change.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Actual Gamma1 transfer and original-form finite characters (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 8,274-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
corrections = []
count = sum(z['exhaustiveTheorems'] for z in certs)
assert count == 110

docpaths = list(dict.fromkeys(r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]))
for f in docpaths:
    assert "\n\n" in f.read_text(encoding="utf-8")
readmes = [(r.parent / "README.md", "Current Project 83 status ("), (repo / "README.md", "Project 83 has an ")]
for f, prefix in readmes:
    assert sum(line.startswith(prefix) for line in f.read_text(encoding="utf-8").splitlines()) == 1
arch = r / "Dubon Architecture.md"
edge = '  GAMMAONEHECKETRACE8274["Literal native Gamma1 trace, Hecke restriction, actual Hecke base change and trace composition proved; surjective-transfer assembly, arithmetic Galois realization and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourcePrimitiveGammaOneHeckeRealizationProductionAudit8290.lean',p/'source-primitive-gamma-one-hecke-realization-8290-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production8290.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/gamma-one-hecke-trace-20261025-599'
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
    "productionModules": 8290, "modules": newmods, "queries": queries,
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
arch.write_text(arch.read_text(encoding='utf-8').replace(edge,'  GAMMAONEHECKETRACE8274["Literal native Gamma1 trace, Hecke restriction, actual Hecke base change and trace composition (DUB-17/18)"] --> PRIMITIVEGAMMAONE8290\n  PRIMITIVEGAMMAONE8290["Actual surjective Gamma1 transfer/Hecke compatibility and original Fourier-valued finite Gamma1 operator characters proved; arithmetic geometric and diamond comparison, Galois realization and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'),encoding='utf-8')



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Actual Gamma1 transfer and original-form finite characters - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-primitive-gamma-one-hecke-realization.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub(r'  logInfo m!".*"\n',
    '  logInfo m!"SOURCE PRIMITIVE GAMMA ONE HECKE REALIZATION AUDIT PASS: {count} theorems including private/generated declarations. The actual surjective Gamma1 transfer intertwines full Hecke operators, and every original primitive form supplies finite Gamma1 operator characters with original Fourier values. Arithmetic geometric and diamond comparison, Galois realization, all-weight association and higher continuation remain open; 16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourcePrimitiveGammaOneHeckeRealizationProductionAudit8290.lean").write_text(out, encoding="utf-8")
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
    target = p / (source.stem + "Production8290.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
(p / "source-primitive-gamma-one-hecke-realization-8290-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 8290, "increment": 16, "queries": 41,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
