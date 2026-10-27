from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 8432
assert d["appliedSourceFrickeCyclotomicFourierSpan"]["receipt8432"]["exit"] == 0
assert (p / "paper-verification-8432-console.exit").read_text().strip() == "0"
assert (r/'Tools/fricke-cyclotomic-fourier-span-20261026-673/canonical-evidence-8432.json').exists()
key = "appliedSourceCuspCyclotomicSpanning"
assert key not in d
digests = {'source-fricke-laurent-independence-2-scratch-receipt.json': '975088C6FE20D9B83CA6988DD3A27862965DE879F6EF6CC0AFD7E78744040612', 'source-fricke-coefficient-twist-8-scratch-receipt.json': '7708C801404E71F1B6D3122C282F047E9F2F2C29358279784714CD2A0179C17D', 'source-fricke-twist-modular-algebra-5-scratch-receipt.json': '488E206F0AFD6EBF47AD5F00B232717C77BCD37259E12B4F47BDDDFEC0852B80', 'source-fricke-elliptic-divisibility-5-scratch-receipt.json': '30EAE535CE426E260D6256DC5E15D0DAFB857C8F173565901F831E9CD623BF75', 'source-fricke-cusp-image-stability-9-scratch-receipt.json': '351ADFCA4A79047C4170CF74B8274DCACA9A491F5C662D86BBD11EA2FD2B7DB9', 'source-cusp-fricke-rational-span-7-scratch-receipt.json': 'C33D8F5A8EC778BE9C5B8C632471A409C1131CD8F862DFA82821E82F29B6C38D', 'source-gamma-one-cyclotomic-cusp-span-3-scratch-receipt.json': '329D1D60D5FC63A8737A0C944BFDEF1F4C0B50D1C7775F4C26C9BDD994AAF80E'}

for name, digest in digests.items():
    assert sha(p / name) == digest
certs = [json.loads((p / name).read_text(encoding="utf-8")) for name in digests]
mods = [m for z in certs for m in z["modules"]]
queries = [q for z in certs for q in z["queries"]]
theorems = [q for z in certs for q in z["theoremRegistrations"]]
defs = [q for z in certs for q in z["constructionRegistrations"]]
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (39, 39, 117, 102, 15)
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
archive_rel='Tools/cusp-cyclotomic-spanning-20261026-685'
evidence=[p/'cusp-cyclotomic-spanning-promotion-route-685.json']
evidence += [p/n for n in ['SourceCuspFrickeRationalSpanAudit7.exit', 'SourceCuspFrickeRationalSpanAudit7.lean', 'SourceCuspFrickeRationalSpanAudit7.log', 'SourceCuspFrickeRationalSpanDependencyAudit7.exit', 'SourceCuspFrickeRationalSpanDependencyAudit7.lean', 'SourceCuspFrickeRationalSpanDependencyAudit7.log', 'SourceFrickeCoefficientTwistAudit8.exit', 'SourceFrickeCoefficientTwistAudit8.lean', 'SourceFrickeCoefficientTwistAudit8.log', 'SourceFrickeCoefficientTwistDependencyAudit8.exit', 'SourceFrickeCoefficientTwistDependencyAudit8.lean', 'SourceFrickeCoefficientTwistDependencyAudit8.log', 'SourceFrickeCuspImageStabilityAudit9.exit', 'SourceFrickeCuspImageStabilityAudit9.lean', 'SourceFrickeCuspImageStabilityAudit9.log', 'SourceFrickeCuspImageStabilityDependencyAudit9.exit', 'SourceFrickeCuspImageStabilityDependencyAudit9.lean', 'SourceFrickeCuspImageStabilityDependencyAudit9.log', 'SourceFrickeEllipticDivisibilityAudit5.exit', 'SourceFrickeEllipticDivisibilityAudit5.lean', 'SourceFrickeEllipticDivisibilityAudit5.log', 'SourceFrickeEllipticDivisibilityDependencyAudit5.exit', 'SourceFrickeEllipticDivisibilityDependencyAudit5.lean', 'SourceFrickeEllipticDivisibilityDependencyAudit5.log', 'SourceFrickeLaurentIndependenceAudit2.exit', 'SourceFrickeLaurentIndependenceAudit2.lean', 'SourceFrickeLaurentIndependenceAudit2.log', 'SourceFrickeLaurentIndependenceDependencyAudit2.exit', 'SourceFrickeLaurentIndependenceDependencyAudit2.lean', 'SourceFrickeLaurentIndependenceDependencyAudit2.log', 'SourceFrickeTwistModularAlgebraAudit5.exit', 'SourceFrickeTwistModularAlgebraAudit5.lean', 'SourceFrickeTwistModularAlgebraAudit5.log', 'SourceFrickeTwistModularAlgebraDependencyAudit5.exit', 'SourceFrickeTwistModularAlgebraDependencyAudit5.lean', 'SourceFrickeTwistModularAlgebraDependencyAudit5.log', 'SourceGammaOneCyclotomicCuspSpanAudit3.exit', 'SourceGammaOneCyclotomicCuspSpanAudit3.lean', 'SourceGammaOneCyclotomicCuspSpanAudit3.log', 'SourceGammaOneCyclotomicCuspSpanDependencyAudit3.exit', 'SourceGammaOneCyclotomicCuspSpanDependencyAudit3.lean', 'SourceGammaOneCyclotomicCuspSpanDependencyAudit3.log', 'consumers683.txt', 'cusp-fricke-rational-span-route-683.json', 'fetch_fricke_cusp_descent_inputs_678.py', 'fricke-coefficient-twist-route-675.json', 'fricke-cusp-descent-input-reuse-assessment-678.json', 'fricke-cusp-image-stability-route-680.json', 'fricke-elliptic-divisibility-route-677.json', 'fricke-laurent-independence-preparer-failure-674.json', 'fricke-laurent-independence-route-674.json', 'fricke-twist-modular-algebra-route-676.json', 'gamma-one-cyclotomic-cusp-span-route-684.json', 'make_cusp_fricke_rational_span_audit_683.py', 'make_fricke_cusp_image_stability_audit_680.py', 'make_fricke_elliptic_divisibility_audit_677.py', 'make_fricke_twist_modular_audit_676.py', 'make_gamma_one_cyclotomic_cusp_span_audit_684.py', 'make_gamma_one_cyclotomic_cusp_span_audit_684b.py', 'make_gamma_one_cyclotomic_cusp_span_audit_684c.py', 'modules683.json', 'prepare_algebraically_closed_fixed_coefficients_681.py', 'prepare_algebraically_closed_fixed_field_681b.py', 'prepare_cusp_fricke_rational_span_audit_683.py', 'prepare_cusp_fricke_rational_span_audit_683b.py', 'prepare_cusp_weight_criterion_679.py', 'prepare_cusp_weight_division_679.py', 'prepare_cusp_weight_transformation_679.py', 'prepare_cusp_weight_transformation_679b.py', 'prepare_fricke_coefficient_twist_audit_675.py', 'prepare_fricke_cusp_image_stability_audit_680.py', 'prepare_fricke_elliptic_divisibility_audit_677.py', 'prepare_fricke_laurent_independence_audit_674b.py', 'prepare_fricke_twist_modular_algebra_audit_676.py', 'prepare_gamma_one_cyclotomic_cusp_span_audit_684.py', 'prepare_twist_stable_subspace_descent_682.py', 'record683.py', 'record_cusp_fricke_rational_span_683.py', 'record_fricke_coefficient_twist_675.py', 'record_fricke_cusp_image_stability_680.py', 'record_fricke_elliptic_divisibility_677.py', 'record_fricke_laurent_independence_674.py', 'record_fricke_twist_modular_algebra_676.py', 'record_gamma_one_cyclotomic_cusp_span_684.py', 'register683.py', 'registrations683.json', 'section683.txt', 'source-cusp-fricke-rational-span-7-audit-config.json', 'source-cusp-fricke-rational-span-7-scratch-receipt.json', 'source-fricke-coefficient-twist-8-audit-config.json', 'source-fricke-coefficient-twist-8-scratch-receipt.json', 'source-fricke-cusp-image-stability-9-audit-config.json', 'source-fricke-cusp-image-stability-9-scratch-receipt.json', 'source-fricke-elliptic-divisibility-5-audit-config.json', 'source-fricke-elliptic-divisibility-5-scratch-receipt.json', 'source-fricke-laurent-independence-2-audit-config.json', 'source-fricke-laurent-independence-2-scratch-receipt.json', 'source-fricke-twist-modular-algebra-5-audit-config.json', 'source-fricke-twist-modular-algebra-5-scratch-receipt.json', 'source-gamma-one-cyclotomic-cusp-span-3-audit-config.json', 'source-gamma-one-cyclotomic-cusp-span-3-scratch-receipt.json', 'status683.txt']]
for folder in ['fricke-scalar-basis-api-failed-675a', 'fricke-scalar-basis-instance-failed-675b', 'fricke-elliptic-power-route-superseded-677a', 'cusp-weight-transformation-preparer-failed-679a', 'cusp-fricke-span-api-failed-683a', 'eisenstein-factor-laurent-diagnostic-684a', 'fricke-cusp-descent-inputs-reuse-678']:
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
supplemental_review_path=r/archive_rel/'cusp-cyclotomic-spanning-promotion-route-685.json'

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
reuse_path = r / "Tools/source-cusp-cyclotomic-spanning.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt8432"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> arithmetic realization of original finite Gamma1 Hecke characters -> actual Picard/H1, full/parabolic, transpose and diamond comparison retaining the original homogeneous coefficient endomorphism -> actual differential/cusp comparison -> rational cusp-form spanning -> cyclotomic Fourier spanning and original weight-image descent.'
discharged = 'Laurent coefficient independence gives a complex basis of the original cyclotomic Fricke span. Its coefficient twist fixes original fractions, commutes with actual modular pullbacks, preserves products and powers, and transports discriminant cusp orders. Holomorphic quotient closure derives the needed elliptic divisibility transport. The exact original E4/E6/Delta weight-image criterion is proved by local monic division and analytic gluing, and every elliptic, cusp and subgroup premise is derived for the twisted image, producing an actual cusp form of the same weight and subgroup. The full algebraically closed fixed-coefficient theorem and finite-support subspace descent are proved and applied to the actual stable image. Injective pullback gives spanning by original cyclotomic Fricke weight images. Laurent division by the proved nonzero Eisenstein factor identifies the original cusp-form Fourier coefficients. Thus the actual Gamma1 weight-two cusp-form space is spanned over the complex numbers by forms whose width-one Fourier coefficients lie in the original cyclotomic field. The general result retains the explicit source balance k+4a+6b=12m; weight two uses a=b=m=1.'
boundary = 'Cyclotomic Fourier spanning is not yet rational Fourier spanning over Q: nontrivial cyclotomic coefficient conjugation and rational descent remain, as do bounded denominators for the original integral-ratio field. Arbitrary Gamma1 cusp differential realization and the converse regular-differential construction remain. The actual Picard/H1, full/parabolic, transpose and diamond comparison must identify original finite homogeneous-coefficient Hecke characters with geometric characters. Frobenius/inertia, arithmetic realization of those characters, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain. No unrestricted odd-weight weight-lowering claim is made, and the all-weight arithmetic goal is unchanged. Complex semisimplicity, finite characters, Witt coefficients and universal deformation rings do not supply a characteristic-zero lift or point. 16/20; DUB-17--20 OPEN.'
status = 'The cyclotomic cusp spanning chain passes 174 exhaustive scratch theorem checks and 117 public axiom queries across 39 modules, with sixteen linters per module and zero diagnostics. Seven declaration-value audits verify 168 required dependencies. Production aggregate, focused audit and sequential foundation/paper verification of the 8,471-module scope are pending.'
route = 'The renewed selected-file search is recorded in Dubon Reuse Search 2026-10-26.md. Reuse actual Laurent germs and analytic injectivity to construct the coefficient twist directly on the original Fricke span, avoiding the external general flatness construction. Holomorphic quotient closure replaces the external monic-growth route for elliptic divisibility. Adapt only the necessary fixed-field, finite-support descent and local cusp-image arguments from the frozen primary sources; native linear algebra pulls the span back. Existing rational Eisenstein and discriminant expansions identify Fourier coefficients by Laurent uniqueness, avoiding recursive unit-division infrastructure. No external full import closure was built or certified. All used and failed audit/helper evidence and retained failed source variants are preserved; only audited mathematical sources are promoted and only imports are qualified. Pins, proof limits, source contract and all twenty acceptance gates are unchanged.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Actual cyclotomic cusp-form spanning (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 8,432-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
corrections = []
count = sum(z['exhaustiveTheorems'] for z in certs)
assert count == 174

docpaths = list(dict.fromkeys(r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]))
for f in docpaths:
    assert "\n\n" in f.read_text(encoding="utf-8")
readmes = [(r.parent / "README.md", "Current Project 83 status ("), (repo / "README.md", "Project 83 has an ")]
for f, prefix in readmes:
    assert sum(line.startswith(prefix) for line in f.read_text(encoding="utf-8").splitlines()) == 1
arch = r / "Dubon Architecture.md"
edge = '  FRICKEFOURIER8432["Original-constant Laurent integral descent, holomorphic summand realization and pole-cleared cyclotomic Fourier span proved. Rational cusp spanning, differential realization, converse, Picard/H1/diamond, original arithmetic association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourceCuspCyclotomicSpanningProductionAudit8471.lean',p/'source-cusp-cyclotomic-spanning-8471-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production8471.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/fricke-cyclotomic-fourier-span-20261026-673'
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
    "productionModules": 8471, "modules": newmods, "queries": queries,
    "theoremRegistrations": theorems, "constructionRegistrations": defs,
    "sourceHashes": {mapping[t.stem]: sha(t) for t, _ in pending}, "scratchCertificates": certs,
    "exactDependency": dependency, "assumptionsDischarged": discharged, "stillOpen": boundary,
    "status": status, "rootPinsChanged": False, "proofLimitsChanged": False,
    "promotionChanges": 'Only scratch imports are qualified. Every final audited statement, proof body and comment is preserved. Original cyclotomic fields, actual Fricke functions, E4/E6/Delta factors, cusp forms, modular pullbacks and width-one q-expansions remain explicit. No source contract is weakened.',
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
arch.write_text(arch.read_text(encoding='utf-8').replace(edge,'  FRICKEFOURIER8432["Original-constant Laurent descent and actual holomorphic Fricke span (DUB-17/18)"] --> CUSPCYCLOTOMIC8471\n  CUSPCYCLOTOMIC8471["Actual cusp-image twist stability, full fixed-field descent and cyclotomic Fourier spanning of Gamma1 weight-two cusp forms proved. Rational descent over Q, bounded denominators, differential realization/converse, Picard/H1/diamond, original all-weight association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'),encoding='utf-8')



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Actual cyclotomic cusp-form spanning - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-cusp-cyclotomic-spanning.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub('  logInfo m!".*"\n', '  logInfo m!"SOURCE CUSP CYCLOTOMIC SPANNING AUDIT PASS: {count} theorems including private/generated declarations. Actual cusp-image twist stability, fixed-field descent and Gamma1 cyclotomic Fourier spanning are proved. Rational descent, differential realization and arithmetic comparison remain; 16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourceCuspCyclotomicSpanningProductionAudit8471.lean").write_text(out, encoding="utf-8")
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
    target = p / (source.stem + "Production8471.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
(p / "source-cusp-cyclotomic-spanning-8471-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 8471, "increment": 39, "queries": 117,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
