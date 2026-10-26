from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 8102
assert d["appliedSourceOriginalPrimitiveProjector"]["receipt8102"]["exit"] == 0
assert (p / "paper-verification-8102-console.exit").read_text().strip() == "0"
key = "appliedSourceOriginalPrimitiveTateImage"
assert key not in d
digests = {'source-original-coefficient-weil-6-scratch-receipt.json': '25FD2B53BA26434FC6CE33B0C52EBEF8C02BA9C2318B8D9FBE7F93B5A8F1F85B', 'source-original-primitive-tate-restriction-8-scratch-receipt.json': 'A2685A2906062D51BA45D445940FA864D0BABC19FCFD726372D899D7BBB526F6', 'source-original-primitive-rank-two-17-scratch-receipt.json': '7099AF0A154C358655F3DB2D704BCAF04E7D34885A80A0A23C5007128DAD1616'}

for name, digest in digests.items():
    assert sha(p / name) == digest
certs = [json.loads((p / name).read_text(encoding="utf-8")) for name in digests]
mods = [m for z in certs for m in z["modules"]]
queries = [q for z in certs for q in z["queries"]]
theorems = [q for z in certs for q in z["theoremRegistrations"]]
defs = [q for z in certs for q in z["constructionRegistrations"]]
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (31, 31, 66, 53, 13)
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
archive_rel='Tools/primitive-tate-image-20261025-563'
evidence=[p/'original-primitive-tate-image-promotion-route-563.json']

evidence += [p/name for name in digests]
evidence += [p/name for name in ['coefficient-weil-route-560.json', 'primitive-tate-restriction-route-561.json', 'primitive-rank-two-route-562b.json', 'prepare_primitive_tate_restriction_audit_561.py', 'prepare_primitive_tate_restriction_audit_561b.py', 'prepare_primitive_rank_two_audit_562.py', 'prepare_primitive_rank_two_dependency_successor_562b.py', 'primitive-rank-two-route-562.json', 'source-original-primitive-rank-two-17-audit-config.json', 'SourceOriginalPrimitiveRankTwoDependencyAudit17.lean', 'SourceOriginalPrimitiveRankTwoDependencyAudit17.log', 'SourceOriginalPrimitiveRankTwoDependencyAudit17.exit', 'record_coefficient_weil_560.py', 'record_primitive_tate_restriction_561.py', 'record_primitive_rank_two_562.py', 'source-original-coefficient-weil-6-audit-config.json', 'source-original-primitive-tate-restriction-8-audit-config.json', 'source-original-primitive-rank-two-17-audit-config-562b.json']]
for cert in certs:
    evidence.append(Path(cert['reuseReview']))

for cert in certs:
    for field in ['log','dependencyAuditLog']:
        f=Path(cert[field]); evidence.extend([f,f.with_suffix('.lean'),f.with_suffix('.exit')])
archive=[]
for source in dict.fromkeys(evidence):
    assert source.exists(),source
    target=r/archive_rel/(source.name+('.txt' if source.suffix=='.lean' else ''))
    assert not target.exists(),target
    refresh_pending.append((target,source.read_bytes(),'Tools'))
    archive.append(dict(source=str(source),path=target.relative_to(r).as_posix(),sha256=sha(source)))
archive_target=r/archive_rel/'archive-manifest.json'
assert not archive_target.exists()
refresh_pending.append((archive_target,(json.dumps(dict(files=archive),indent=2)+'\n').encode(),'Tools'))
supplemental_review_path=r/archive_rel/'original-primitive-tate-image-promotion-route-563.json'

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
reuse_path = r / "Tools/source-original-primitive-tate-image.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt8102"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> residual association -> primitive Frobenius determinant -> nonzero required primitive component pairing -> nondegenerate rank-two image of the actual arithmetic projector on the original coefficient-extended Tate module'
discharged = 'The original rational Weil pairing remains injective after extension to the actual coefficient field, with its alternating, good-prime Hecke adjointness and cyclotomic multiplier identities. The proved integral cusp/lattice relations factor the actual original Tate action through the same integral Hecke algebra used by the arithmetic projector. Literal coefficient extension preserves its prime operators and polynomial, so the actual projected operator is idempotent and self-adjoint. Existing all-word original rank-two Tate coordinates and native finite-product scalar extension identify its image: the prescribed p-adic Hecke character has value one on the projector and gives its scalar action, making the actual image rank two. The same projector therefore has a nonzero rank-two image with an injective restriction of the literal root-valued Weil pairing. Action comparison, generator, character-compatibility, image-dimension and restricted-nondegeneracy assumptions are all discharged by actual upstream objects.'
boundary = 'Comparison of this image with the existing spanning primitive specialization, the separate primitive Frobenius determinant, residual association, arithmetic automorphy and all-weight continuation remain required. The Frobenius quadratic identity alone does not prove the determinant. 16/20; DUB-17--20 OPEN.'
status = 'The actual nondegenerate rank-two primitive Tate image passes 140 exhaustive scratch checks and 66 explicit axiom queries across 31 modules, with sixteen linters per module and zero diagnostics. Three declaration-value audits verify 91 required dependencies. Three additional public coordinate identities are separately axiom-checked as reflexivity proofs; no erased named dependency is claimed. Production aggregate, focused audit and sequential foundation/paper verification of the 8,133-module scope are pending.'
route = 'Reuse native finite-source Hom base change and flat tensor injection, with no finiteness assumption on the root-valued target. Reuse the original cusp/lattice Hecke relations, all-word rank-two Tate coordinates, prescribed p-adic eigencharacter, algebraIdempotentLeftIdeal and native range/finite-product equivalences. Only good-prime adjointness enters the projector. The same arithmetic projector supplies both rank two and restricted Weil nondegeneracy. Next reuse native range_liftBaseChange to compare with the existing spanning specialization; retain the original representation. No second determinant descent, new eigencharacter, generic Jacobian representability, external import, root pin change or proof-limit change is introduced.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Actual nondegenerate rank-two primitive Tate image (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 8,102-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
corrections = []
count = sum(z['exhaustiveTheorems'] for z in certs)
assert count == 140

docpaths = list(dict.fromkeys(r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]))
for f in docpaths:
    assert "\n\n" in f.read_text(encoding="utf-8")
readmes = [(r.parent / "README.md", "Current Project 83 status ("), (repo / "README.md", "Project 83 has an ")]
for f, prefix in readmes:
    assert sum(line.startswith(prefix) for line in f.read_text(encoding="utf-8").splitlines()) == 1
arch = r / "Dubon Architecture.md"
edge = '  PRIMITIVEPROJECTOR8102["Actual rational Weil nondegeneracy and nonzero arithmetic primitive idempotent; original Tate realization, component restriction and determinant OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourceOriginalPrimitiveTateImageProductionAudit8133.lean',p/'source-original-primitive-tate-image-8133-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production8133.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/primitive-projector-20261025-559'
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
    "productionModules": 8133, "modules": newmods, "queries": queries,
    "theoremRegistrations": theorems, "constructionRegistrations": defs,
    "sourceHashes": {mapping[t.stem]: sha(t) for t, _ in pending}, "scratchCertificates": certs,
    "exactDependency": dependency, "assumptionsDischarged": discharged, "stillOpen": boundary,
    "status": status, "rootPinsChanged": False, "proofLimitsChanged": False,
    "promotionChanges": 'Only scratch imports are qualified. Every mathematical statement, proof body and module comment is preserved. The original rational Tate module and root-valued Weil pairing, actual cusp forms, integral Hecke algebra and prescribed primitive coefficient field retain their definitions. No source contract is weakened.',
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
arch.write_text(arch.read_text(encoding='utf-8').replace(edge, '  PRIMITIVEPROJECTOR8102["Actual rational Weil nondegeneracy and nonzero arithmetic primitive idempotent (DUB-17/18)"] --> PRIMITIVETATEIMAGE8133\n  PRIMITIVETATEIMAGE8133["Actual nondegenerate rank-two primitive Tate image; spanning-specialization comparison and determinant OPEN (DUB-17/18)"] --> CMARITH4538'),encoding='utf-8')



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Actual nondegenerate rank-two primitive Tate image - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-original-primitive-tate-image.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub(r'  logInfo m!".*"\n',
    '  logInfo m!"SOURCE ORIGINAL PRIMITIVE TATE IMAGE AUDIT PASS: {count} theorems including private/generated declarations. The actual arithmetic projector has a nonzero rank-two original Tate image with an injective restricted Weil pairing. Comparison to the existing spanning specialization, determinant, residual association, automorphy and all-weight continuation remain open; 16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourceOriginalPrimitiveTateImageProductionAudit8133.lean").write_text(out, encoding="utf-8")
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
    target = p / (source.stem + "Production8133.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
(p / "source-original-primitive-tate-image-8133-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 8133, "increment": 31, "queries": 66,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
