from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 8159
assert d["appliedSourceOriginalPrimitiveFrobenius"]["receipt8159"]["exit"] == 0
assert (p / "paper-verification-8159-console.exit").read_text().strip() == "0"
key = "appliedSourcePrimitiveResidualAssociation"
assert key not in d
digests = {'source-original-prescribed-completion-11-scratch-receipt.json': '85897B04E83F43398B1719464DA526036996B8E2CB1F9070D6A1D7869D766C91', 'source-original-arithmetic-residual-11-scratch-receipt.json': '23E3F0ECE0916F6867C5C78572F5B4E21543AA8DF1A75F59911C7ABCFAD35803', 'source-primitive-residual-galois-12-scratch-receipt.json': 'EC9B028F14F9E7893497B95CAAAF2F263D228554811405FC0A6A3434E97B4DA8'}

for name, digest in digests.items():
    assert sha(p / name) == digest
certs = [json.loads((p / name).read_text(encoding="utf-8")) for name in digests]
mods = [m for z in certs for m in z["modules"]]
queries = [q for z in certs for q in z["queries"]]
theorems = [q for z in certs for q in z["theoremRegistrations"]]
defs = [q for z in certs for q in z["constructionRegistrations"]]
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (34, 34, 58, 52, 6)
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
archive_rel='Tools/primitive-residual-20261025-573'
evidence=[p/'primitive-residual-association-promotion-route-573.json']

evidence += [p/name for name in digests]
evidence += [p/name for name in ['prescribed-completion-route-568b.json', 'arithmetic-residual-route-570.json', 'primitive-residual-galois-route-571b.json', 'prepare_prescribed_completion_audit_568.py', 'prepare_prescribed_completion_audit_568b.py', 'repair_prescribed_completion_documentation_568b.py', 'record_prescribed_completion_568.py', 'prescribed-completion-route-568.json', 'prescribed-completion-documentation-successor-568b.json', 'SourceOriginalPrescribedCompletionAudit11.lean', 'SourceOriginalPrescribedCompletionAudit11.log', 'SourceOriginalPrescribedCompletionAudit11.exit', 'SourceOriginalPrescribedCompletionDependencyAudit11.lean', 'prepare_arithmetic_residual_audit_570.py', 'record_arithmetic_residual_570.py', 'prepare_primitive_residual_galois_audit_571.py', 'record_primitive_residual_galois_571.py', 'record_primitive_residual_galois_571b.py', 'primitive-residual-galois-route-571.json', 'primitive-residual-galois-route-successor-571b.json', 'source-original-prescribed-completion-11-audit-config.json', 'source-original-prescribed-completion-11-audit-config-568b.json', 'source-original-arithmetic-residual-11-audit-config.json', 'source-primitive-residual-galois-12-audit-config.json']]
evidence += sorted((p/'prescribed-completion-568-pre-doc-audit').iterdir())
for cert in certs:
    evidence.append(Path(cert['reuseReview']))

for cert in certs:
    for field in ['log','dependencyAuditLog']:
        f=Path(cert[field]); evidence.extend([f,f.with_suffix('.lean'),f.with_suffix('.exit')])
archive=[]
for source in dict.fromkeys(evidence):
    assert source.exists(),source
    target=r/archive_rel/('prescribed-completion-568-pre-doc-audit' if source.parent.name=='prescribed-completion-568-pre-doc-audit' else '')/(source.name+('.txt' if source.suffix=='.lean' else ''))
    assert not target.exists(),target
    refresh_pending.append((target,source.read_bytes(),'Tools'))
    archive.append(dict(source=str(source),path=target.relative_to(r).as_posix(),sha256=sha(source)))
archive_target=r/archive_rel/'archive-manifest.json'
assert not archive_target.exists()
refresh_pending.append((archive_target,(json.dumps(dict(files=archive),indent=2)+'\n').encode(),'Tools'))
supplemental_review_path=r/archive_rel/'primitive-residual-association-promotion-route-573.json'

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
reuse_path = r / "Tools/source-primitive-residual-association.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt8159"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> actual all-weight primitive Galois association -> close the residual association branch at the original arithmetic support Qp, with the original Fourier coefficients, weight determinant and good-prime inertia'
discharged = 'For every original primitive form of weight at least two and every prescribed rational prime, construct the actual finite local coefficient field, residue closure of that characteristic and continuous residual representation on the original arithmetic group of support Qp. Its good-prime Frobenius trace is the reduction of the original Fourier coefficient, its determinant is q^(k-1), and its good-prime inertia is trivial. The prescribed algebraic-integer reduction selects the coefficient completion and residue map. Actual norm-local Frobenius and inertia are compared with the source valuation, and the representation descends through the arithmetic quotient. The parabolic alternative is eliminated by actual Petersson-adjoint level descent and normalization to a primitive divisor; the existing weight twist and support equality restore the original weight and level. None of these steps remains an additional representation, coefficient-field, local-compatibility or parabolic-realization hypothesis.'
boundary = 'The global residual determinant identity, all-weight adic realization and required local, regularity and image properties, arithmetic automorphy and literal higher symmetric-power continuation remain required. This closes residual association, not the full Galois or analytic endpoint. 16/20; DUB-17--20 OPEN.'
status = 'The all-weight original-support residual association passes 137 exhaustive scratch checks and 58 explicit axiom queries across 34 modules, with sixteen linters per module and zero diagnostics. Three declaration-value audits verify 103 required dependencies. The failed documentation audit and its unchanged-mathematics successor, and the route-serialization failure and corrected successor, are preserved. Production aggregate, focused audit and sequential foundation/paper verification of the 8,193-module scope are pending.'
route = 'Reuse the native completion and residue equivalences, finite Galois factors and original arithmetic support embeddings; reuse the proved Petersson inner product, commuting Hecke eigenvectors, newform normalization, residual weight-two reduction, cyclotomic twist and support comparison. The same original coefficients and exact source local actions are retained. No external import, root pin change, proof-limit change or incidental generalization is used.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Actual all-weight original-support residual association (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 8,159-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
corrections = []
count = sum(z['exhaustiveTheorems'] for z in certs)
assert count == 137

docpaths = list(dict.fromkeys(r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]))
for f in docpaths:
    assert "\n\n" in f.read_text(encoding="utf-8")
readmes = [(r.parent / "README.md", "Current Project 83 status ("), (repo / "README.md", "Project 83 has an ")]
for f, prefix in readmes:
    assert sum(line.startswith(prefix) for line in f.read_text(encoding="utf-8").splitlines()) == 1
arch = r / "Dubon Architecture.md"
edge = '  PRIMITIVEFROBENIUS8159["Same original primitive representation: cyclotomic determinant, exact Frobenius polynomial and prescribed-embedding residual realization; source reduction, arithmetic quotient and norm-local comparisons OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourcePrimitiveResidualAssociationProductionAudit8193.lean',p/'source-primitive-residual-association-8193-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production8193.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/primitive-frobenius-20261025-569'
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
    "productionModules": 8193, "modules": newmods, "queries": queries,
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
arch.write_text(arch.read_text(encoding='utf-8').replace(edge, '  PRIMITIVEFROBENIUS8159["Same original primitive representation: cyclotomic determinant, exact Frobenius polynomial and prescribed-embedding residual realization (DUB-17/18)"] --> PRIMITIVERESIDUAL8193\n  PRIMITIVERESIDUAL8193["All-weight original-support residual association: coefficient completion, norm-local comparison, arithmetic descent and parabolic closure proved; global determinant, adic realization, local/image properties and automorphy OPEN (DUB-17/18)"] --> CMARITH4538'),encoding='utf-8')



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Actual all-weight original-support residual association - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-primitive-residual-association.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub(r'  logInfo m!".*"\n',
    '  logInfo m!"SOURCE PRIMITIVE RESIDUAL ASSOCIATION AUDIT PASS: {count} theorems including private/generated declarations. The actual original primitive form in every weight at least two supplies its prescribed-characteristic residual representation on the original support, with exact original coefficient reduction, weight determinant and good-prime inertia. Global determinant, adic realization, local/image properties, automorphy and all-weight continuation remain open; 16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourcePrimitiveResidualAssociationProductionAudit8193.lean").write_text(out, encoding="utf-8")
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
    target = p / (source.stem + "Production8193.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
(p / "source-primitive-residual-association-8193-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 8193, "increment": 34, "queries": 58,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
