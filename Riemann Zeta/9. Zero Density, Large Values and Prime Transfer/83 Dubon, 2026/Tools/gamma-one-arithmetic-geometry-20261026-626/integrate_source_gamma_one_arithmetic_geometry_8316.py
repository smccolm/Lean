from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 8290
assert d["appliedSourcePrimitiveGammaOneHeckeRealization"]["receipt8290"]["exit"] == 0
assert (p / "paper-verification-8290-console.exit").read_text().strip() == "0"
assert (r/'Tools/primitive-gamma-one-hecke-20261026-618/canonical-evidence-8290.json').exists()
key = "appliedSourceGammaOneArithmeticGeometry"
assert key not in d
digests = {'source-gamma-one-function-field-10b-scratch-receipt.json': '5AF3D767A3394701B100CC68733AE6269D9AEE63AF52D88D08C9A3D0B5DE1C87', 'source-gamma-one-hecke-field-5-scratch-receipt.json': '33716CDDC0E17FC2B1864D84CE01001A2AB8F7CCA0E056FBDAF5CD113AB48DC9', 'source-gamma-one-hecke-picard-2b-scratch-receipt.json': '0A82D7E6B206DC3CA34AF22C2CA6C16E8356AD3AE16A058E41C935F2D5ECA709', 'source-gamma-one-arithmetic-9-scratch-receipt.json': '168F5541A452ABB2C66949AE9D421F9DF0555C3927BCFA1C49CED9AC46E32553'}

for name, digest in digests.items():
    assert sha(p / name) == digest
certs = [json.loads((p / name).read_text(encoding="utf-8")) for name in digests]
mods = [m for z in certs for m in z["modules"]]
queries = [q for z in certs for q in z["queries"]]
theorems = [q for z in certs for q in z["theoremRegistrations"]]
defs = [q for z in certs for q in z["constructionRegistrations"]]
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (26, 26, 102, 77, 25)
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
archive_rel='Tools/gamma-one-arithmetic-geometry-20261026-626'
evidence=[p/'gamma-one-arithmetic-geometry-promotion-route-626.json']
evidence += [p/n for n in ['SourceGammaOneArithmeticAudit9.exit', 'SourceGammaOneArithmeticAudit9.lean', 'SourceGammaOneArithmeticAudit9.log', 'SourceGammaOneArithmeticDependencyAudit9.exit', 'SourceGammaOneArithmeticDependencyAudit9.lean', 'SourceGammaOneArithmeticDependencyAudit9.log', 'SourceGammaOneFunctionField-before-pruning-620.lean.txt', 'SourceGammaOneFunctionFieldAudit10.exit', 'SourceGammaOneFunctionFieldAudit10.lean', 'SourceGammaOneFunctionFieldAudit10.log', 'SourceGammaOneFunctionFieldAudit10b.exit', 'SourceGammaOneFunctionFieldAudit10b.lean', 'SourceGammaOneFunctionFieldAudit10b.log', 'SourceGammaOneFunctionFieldDependencyAudit10.lean', 'SourceGammaOneFunctionFieldDependencyAudit10b.exit', 'SourceGammaOneFunctionFieldDependencyAudit10b.lean', 'SourceGammaOneFunctionFieldDependencyAudit10b.log', 'SourceGammaOneHeckeFieldAudit5.exit', 'SourceGammaOneHeckeFieldAudit5.lean', 'SourceGammaOneHeckeFieldAudit5.log', 'SourceGammaOneHeckeFieldDependencyAudit5.exit', 'SourceGammaOneHeckeFieldDependencyAudit5.lean', 'SourceGammaOneHeckeFieldDependencyAudit5.log', 'SourceGammaOneHeckePicardAudit2.exit', 'SourceGammaOneHeckePicardAudit2.lean', 'SourceGammaOneHeckePicardAudit2.log', 'SourceGammaOneHeckePicardAudit2b.exit', 'SourceGammaOneHeckePicardAudit2b.lean', 'SourceGammaOneHeckePicardAudit2b.log', 'SourceGammaOneHeckePicardDependencyAudit2.exit', 'SourceGammaOneHeckePicardDependencyAudit2.lean', 'SourceGammaOneHeckePicardDependencyAudit2.log', 'SourceGammaOneHeckePicardDependencyAudit2b.exit', 'SourceGammaOneHeckePicardDependencyAudit2b.lean', 'SourceGammaOneHeckePicardDependencyAudit2b.log', 'consumers622.txt', 'fetch_gamma1_geometric_reuse_619b.py', 'fetch_gamma1_hecke_correspondence_reuse_621.py', 'gamma-one-finite-fields-preexecution-review-8305.json', 'gamma-one-finite-fields-promotion-route-623.json', 'gamma1-actual-picard-hecke-route-624.json', 'gamma1-actual-picard-hecke-route-624b.json', 'gamma1-arithmetic-hecke-picard-route-625.json', 'gamma1-finite-hecke-field-route-622.json', 'gamma1-function-field-finite-route-620.json', 'gamma1-function-field-finite-route-620b.json', 'gamma1-geometric-reuse-assessment-619.json', 'gamma1-hecke-correspondence-reuse-assessment-621.json', 'modules622.json', 'normalize_gamma_one_rational_algebra_620.py', 'prepare_gamma_one_arithmetic_audit_625.py', 'prepare_gamma_one_arithmetic_picard_625.py', 'prepare_gamma_one_arithmetic_scope_625.py', 'prepare_gamma_one_finite_fields_promotion_8305.py', 'prepare_gamma_one_function_field_audit_620.py', 'prepare_gamma_one_function_field_audit_620b.py', 'prepare_gamma_one_hecke_arithmetic_625.py', 'prepare_gamma_one_hecke_field_audit_622.py', 'prepare_gamma_one_hecke_field_scope_622.py', 'prepare_gamma_one_hecke_picard_audit_624.py', 'prepare_gamma_one_hecke_picard_audit_624b.py', 'prepare_gamma_one_hecke_picard_scope_624.py', 'prepare_gamma_one_hecke_picard_successor_624b.py', 'record622.py', 'record_gamma_one_arithmetic_625.py', 'record_gamma_one_function_field_620.py', 'record_gamma_one_function_field_620b.py', 'record_gamma_one_hecke_field_622.py', 'record_gamma_one_hecke_picard_624.py', 'record_gamma_one_hecke_picard_624b.py', 'register622.py', 'registrations622.json', 'section622.txt', 'source-gamma-one-arithmetic-9-audit-config.json', 'source-gamma-one-arithmetic-9-scratch-receipt.json', 'source-gamma-one-function-field-10-audit-config.json', 'source-gamma-one-function-field-10b-audit-config.json', 'source-gamma-one-function-field-10b-scratch-receipt.json', 'source-gamma-one-hecke-field-5-audit-config.json', 'source-gamma-one-hecke-field-5-scratch-receipt.json', 'source-gamma-one-hecke-picard-2-audit-config.json', 'source-gamma-one-hecke-picard-2b-audit-config.json', 'source-gamma-one-hecke-picard-2b-scratch-receipt.json', 'status622.txt']]
for folder in ['gamma1-function-field-620-before-definition-docstrings', 'gamma1-hecke-fields-622-before-explicit-inclusion-projection', 'gamma1-geometric-reuse-619', 'gamma1-hecke-correspondence-reuse-621']:
    evidence += sorted(f for f in (p/folder).rglob("*") if f.is_file())
for cert in certs:
    evidence.append(Path(cert['reuseReview']))

for cert in certs:
    for field in ['log','dependencyAuditLog']:
        f=Path(cert[field]); evidence.extend([f,f.with_suffix('.lean'),f.with_suffix('.exit')])
archive=[]
for source in dict.fromkeys(evidence):
    assert source.exists(),source
    target=r/archive_rel/source.relative_to(p)
    if source.suffix=='.lean':target=target.with_name(target.name+'.txt')
    assert not target.exists(),target
    refresh_pending.append((target,source.read_bytes(),'Tools'))
    archive.append(dict(source=str(source),path=target.relative_to(r).as_posix(),sha256=sha(source)))
archive_target=r/archive_rel/'archive-manifest.json'
assert not archive_target.exists()
refresh_pending.append((archive_target,(json.dumps(dict(files=archive),indent=2)+'\n').encode(),'Tools'))
supplemental_review_path=r/archive_rel/'gamma-one-arithmetic-geometry-promotion-route-626.json'

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
reuse_path = r / "Tools/source-gamma-one-arithmetic-geometry.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt8290"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero Galois association -> arithmetic realization of original finite Gamma1 Hecke characters -> geometric/H1 comparison retaining the original homogeneous coefficient action, and diamond comparison -> actual Gamma1 finite fields, Picard correspondence and arithmetic Hecke equivariance.'
discharged = 'The actual Gamma1 and Hecke function fields are finite over the original transcendental j coordinate, including after Laurent scalar extension. Native modular norms, original level-one j polynomials, Laurent independence and primitive elements derive rational polynomial relations and finite degree. Native modular translation and existing sparse sums prove the integral expansion of the actual form f(dz); literal q-substitution therefore defines the second Hecke field map. Both field maps are finite by existing coordinate exchange. Their proved closed constant residues and existing divisor norm/degree identities construct the actual Picard Hecke operator. Coefficient transport preserves the same fields, fixes original j under arithmetic automorphisms, and commutes with both maps. The genuine arithmetic place action preserves normalized order, degree and principal divisors; native quotient functoriality gives the actual Gamma1 Picard Galois action and its torsion stability. Place restriction and ramification identities prove that this action commutes with the actual Picard Hecke operator. No finite-coordinate, field-preservation, finite-map, residue-degree, degree/principal-preservation or arithmetic-equivariance premise remains.'
boundary = 'The geometric/H1 comparison must retain the original homogeneous matrix coefficient action and prove the upper/lower correspondence and transpose/diamond conventions. Arithmetic equivariance of the ordinary Picard operator alone does not identify the original binary-coefficient finite Hecke characters with geometric characters. Diamond comparison, Frobenius/inertia, arithmetic Galois realization of these finite characters, original all-weight characteristic-zero association, required local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain required. No characteristic-zero character lift or deformation point is inferred. 16/20; DUB-17--20 OPEN.'
status = 'The actual Gamma1 finite-field, Picard and arithmetic-Hecke chain passes 185 exhaustive scratch checks and 102 explicit public axiom queries across 26 modules, with sixteen linters per module and zero diagnostics. Four declaration-value audits verify 144 required dependencies. Production aggregate, focused audit and sequential foundation/paper verification of the 8,316-module scope are pending.'
route = 'Renewed primary inspection selects actual Gamma1 integral-ratio and finite-coordinate arguments from the frozen Anthropic snapshot. Its inspected adic theorem still requires a characteristic-zero Hecke-and-diamond character; the separate Gamma0 result is residual over a field. Reuse original j, native modular norms, existing level-one polynomials, Laurent independence, scalar-extension finiteness, native modular translation, original dilation and sparse sums. Existing coordinate exchange, closed residues, divisor norm/degree formulas, inverse-coefficient place transport and quotient action laws supply the full Picard/arithmetic construction. External alternate coordinates, duplicate cusp/scalar-extension development, conditional fallback maps and an abstract semilinear framework are deferred. Explicit inclusion projection and composition avoid kernel/rewrite unfolding without changing limits. Missing docstrings and construction-root dependency accounting have fresh audits; all failed evidence is preserved. Root pins and full source contracts are unchanged.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Actual Gamma1 arithmetic geometry and Hecke equivariance (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 8,290-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
corrections = []
count = sum(z['exhaustiveTheorems'] for z in certs)
assert count == 185

docpaths = list(dict.fromkeys(r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]))
for f in docpaths:
    assert "\n\n" in f.read_text(encoding="utf-8")
readmes = [(r.parent / "README.md", "Current Project 83 status ("), (repo / "README.md", "Project 83 has an ")]
for f, prefix in readmes:
    assert sum(line.startswith(prefix) for line in f.read_text(encoding="utf-8").splitlines()) == 1
arch = r / "Dubon Architecture.md"
edge = '  PRIMITIVEGAMMAONE8290["Actual surjective Gamma1 transfer/Hecke compatibility and original Fourier-valued finite Gamma1 operator characters proved; arithmetic geometric and diamond comparison, Galois realization and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourceGammaOneArithmeticGeometryProductionAudit8316.lean',p/'source-gamma-one-arithmetic-geometry-8316-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production8316.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/primitive-gamma-one-hecke-20261026-618'
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
    "productionModules": 8316, "modules": newmods, "queries": queries,
    "theoremRegistrations": theorems, "constructionRegistrations": defs,
    "sourceHashes": {mapping[t.stem]: sha(t) for t, _ in pending}, "scratchCertificates": certs,
    "exactDependency": dependency, "assumptionsDischarged": discharged, "stillOpen": boundary,
    "status": status, "rootPinsChanged": False, "proofLimitsChanged": False,
    "promotionChanges": 'Only scratch imports are qualified. Every audited statement, proof body and comment is preserved. Actual modular forms, original j, integral expansions, literal Laurent fields and both finite field maps retain their definitions. No source contract is weakened.',
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
arch.write_text(arch.read_text(encoding='utf-8').replace(edge,'  PRIMITIVEGAMMAONE8290["Actual surjective Gamma1 transfer/Hecke compatibility and original Fourier-valued finite Gamma1 operator characters (DUB-17/18)"] --> GAMMAONEFIELDS8316\n  GAMMAONEFIELDS8316["Actual Gamma1 fields, finite maps, Picard Hecke and arithmetic equivariance proved. Original homogeneous-coefficient H1/diamond comparison, Frobenius/inertia, all-weight Galois realization and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'),encoding='utf-8')



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Actual Gamma1 arithmetic geometry and Hecke equivariance - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-gamma-one-arithmetic-geometry.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub(r'  logInfo m!".*"\n',
    '  logInfo m!"SOURCE GAMMA ONE ARITHMETIC GEOMETRY AUDIT PASS: {count} theorems including private/generated declarations. Actual Gamma1 fields and finite maps construct the genuine Picard Hecke operator and arithmetic action; their Hecke equivariance and torsion stability are proved. Original homogeneous-coefficient H1/diamond comparison, Frobenius/inertia, all-weight association and higher continuation remain open; 16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourceGammaOneArithmeticGeometryProductionAudit8316.lean").write_text(out, encoding="utf-8")
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
    target = p / (source.stem + "Production8316.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
(p / "source-gamma-one-arithmetic-geometry-8316-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 8316, "increment": 26, "queries": 102,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
