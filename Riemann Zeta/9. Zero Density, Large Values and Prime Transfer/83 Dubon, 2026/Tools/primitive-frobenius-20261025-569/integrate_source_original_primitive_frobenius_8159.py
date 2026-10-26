from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 8133
assert d["appliedSourceOriginalPrimitiveTateImage"]["receipt8133"]["exit"] == 0
assert (p / "paper-verification-8133-console.exit").read_text().strip() == "0"
key = "appliedSourceOriginalPrimitiveFrobenius"
assert key not in d
digests = {'source-original-primitive-cyclotomic-12-scratch-receipt.json': '8C259D737D6F18B54B7A8AA76258ECB9ED780D0C8A047DD1FF0A1FAB79862F91', 'source-original-primitive-frobenius-charpoly-5-scratch-receipt.json': 'B66051491071B42B756DAE81D7DBD227E5E9FD14DFB296429F97EB8ABCC589AD', 'source-original-primitive-residual-frobenius-7-scratch-receipt.json': 'CCBBFF7F47B1F7FA620AF064D4E560663975A59013B1086256C9557863E47F2C', 'source-original-prescribed-residual-frobenius-2-scratch-receipt.json': 'B5AEDE141A244064F3403B542D20A357353BEA95717BCDD43F9421FBF93E8314'}

for name, digest in digests.items():
    assert sha(p / name) == digest
certs = [json.loads((p / name).read_text(encoding="utf-8")) for name in digests]
mods = [m for z in certs for m in z["modules"]]
queries = [q for z in certs for q in z["queries"]]
theorems = [q for z in certs for q in z["theoremRegistrations"]]
defs = [q for z in certs for q in z["constructionRegistrations"]]
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (26, 26, 50, 48, 2)
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
archive_rel='Tools/primitive-frobenius-20261025-569'
evidence=[p/'original-primitive-frobenius-promotion-route-569.json']

evidence += [p/name for name in digests]
evidence += [p/name for name in ['primitive-cyclotomic-route-564.json', 'primitive-frobenius-charpoly-route-565.json', 'primitive-residual-frobenius-route-566.json', 'prescribed-residual-frobenius-route-567b.json', 'prepare_primitive_cyclotomic_audit_564.py', 'record_primitive_cyclotomic_564.py', 'prepare_primitive_frobenius_charpoly_audit_565.py', 'record_primitive_frobenius_charpoly_565.py', 'prepare_primitive_residual_frobenius_audit_566.py', 'record_primitive_residual_frobenius_566.py', 'prepare_prescribed_residual_frobenius_audit_567.py', 'prepare_prescribed_residual_dependency_successor_567b.py', 'record_prescribed_residual_frobenius_567.py', 'prescribed-residual-frobenius-route-567.json', 'source-original-prescribed-residual-frobenius-2-audit-config.json', 'SourceOriginalPrescribedResidualFrobeniusDependencyAudit2.lean', 'SourceOriginalPrescribedResidualFrobeniusDependencyAudit2.log', 'SourceOriginalPrescribedResidualFrobeniusDependencyAudit2.exit', 'source-original-primitive-cyclotomic-12-audit-config.json', 'source-original-primitive-frobenius-charpoly-5-audit-config.json', 'source-original-primitive-residual-frobenius-7-audit-config.json', 'source-original-prescribed-residual-frobenius-2-audit-config-567b.json']]
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
supplemental_review_path=r/archive_rel/'original-primitive-frobenius-promotion-route-569.json'

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
reuse_path = r / "Tools/source-original-primitive-frobenius.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt8133"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> all-weight residual association -> weight-two prescribed residual realization -> the actual primitive original Tate representation has arithmetic Frobenius characteristic polynomial X^2-a_q*X+q and trivial good-prime inertia -> compare the actual rank-two projector image and transport its literal Weil pairing through the existing spanning specialization'
discharged = 'The actual arithmetic projector image is identified with the existing spanning primitive specialization. Its literal root-valued alternating Weil pairing is nondegenerate and has the original cyclotomic multiplier, so the same representation has cyclotomic determinant. The exact source valuation arithmetic Frobenius acts on prime-to-q roots by q-th powers, giving cyclotomic value q. The original Tate quadratic relation therefore yields determinant q, trace a_q and characteristic polynomial X^2-a_q*X+q. The already constructed integral lattice and literal residue representation retain this polynomial and trivial good-prime inertia. A prescribed Fourier-field embedding is retained through the actual continuous Tate specialization, stable lattice and residual construction. No separate determinant, nondegenerate pairing, Frobenius action, stable lattice or residual compatibility hypothesis is supplied.'
boundary = 'Choosing the coefficient completion and residue embedding compatible with the source prescribed algebraic-integer reduction, the arithmetic quotient and norm-local comparisons, closure of the parabolic branch, final weight twist and support comparison, arithmetic automorphy and all-weight continuation remain required. The prescribed-embedding theorem explicitly assumes a genuine finite local coefficient field and valuation extension, to be discharged by the chosen completion. 16/20; DUB-17--20 OPEN.'
status = 'The actual primitive Frobenius and prescribed residual realization passes 74 exhaustive scratch checks and 50 explicit axiom queries across 26 modules, with sixteen linters per module and zero diagnostics. Four declaration-value audits verify 98 required dependencies. The original failed dependency-name audit is preserved with its passing corrected successor; no proof source changed. Production aggregate, focused audit and sequential foundation/paper verification of the 8,159-module scope are pending.'
route = 'Reuse native range_liftBaseChange, finite-dimensional bijectivity and alternating two-coordinate determinant algebra to retain the original representation. Reuse source valuation root lifting, PadicInt.ext_of_toZModPow, the exact cyclotomic character and native Cayley-Hamilton. Reuse the existing stable lattice and literal entrywise reduction with native characteristic-polynomial transport. Preserve an arbitrary prescribed Fourier-field embedding, then choose the completion at the kernel of the source reduction using the proved quotient/residue equivalence. No external import, root pin change, proof-limit change or generic Jacobian infrastructure is needed.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Actual primitive Frobenius and prescribed residual realization (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 8,133-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
corrections = []
count = sum(z['exhaustiveTheorems'] for z in certs)
assert count == 74

docpaths = list(dict.fromkeys(r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]))
for f in docpaths:
    assert "\n\n" in f.read_text(encoding="utf-8")
readmes = [(r.parent / "README.md", "Current Project 83 status ("), (repo / "README.md", "Project 83 has an ")]
for f, prefix in readmes:
    assert sum(line.startswith(prefix) for line in f.read_text(encoding="utf-8").splitlines()) == 1
arch = r / "Dubon Architecture.md"
edge = '  PRIMITIVETATEIMAGE8133["Actual nondegenerate rank-two primitive Tate image; spanning-specialization comparison and determinant OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourceOriginalPrimitiveFrobeniusProductionAudit8159.lean',p/'source-original-primitive-frobenius-8159-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production8159.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/primitive-tate-image-20261025-563'
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
    "productionModules": 8159, "modules": newmods, "queries": queries,
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
arch.write_text(arch.read_text(encoding='utf-8').replace(edge, '  PRIMITIVETATEIMAGE8133["Actual nondegenerate rank-two primitive Tate image (DUB-17/18)"] --> PRIMITIVEFROBENIUS8159\n  PRIMITIVEFROBENIUS8159["Same original primitive representation: cyclotomic determinant, exact Frobenius polynomial and prescribed-embedding residual realization; source reduction, arithmetic quotient and norm-local comparisons OPEN (DUB-17/18)"] --> CMARITH4538'),encoding='utf-8')



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Actual primitive Frobenius and prescribed residual realization - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-original-primitive-frobenius.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub(r'  logInfo m!".*"\n',
    '  logInfo m!"SOURCE ORIGINAL PRIMITIVE FROBENIUS AUDIT PASS: {count} theorems including private/generated declarations. The same original primitive representation has cyclotomic determinant, exact Frobenius trace/determinant/characteristic polynomial, and a prescribed-embedding residual realization. Source reduction compatibility, arithmetic quotient and norm-local comparisons, automorphy and all-weight continuation remain open; 16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourceOriginalPrimitiveFrobeniusProductionAudit8159.lean").write_text(out, encoding="utf-8")
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
    target = p / (source.stem + "Production8159.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
(p / "source-original-primitive-frobenius-8159-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 8159, "increment": 26, "queries": 50,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
