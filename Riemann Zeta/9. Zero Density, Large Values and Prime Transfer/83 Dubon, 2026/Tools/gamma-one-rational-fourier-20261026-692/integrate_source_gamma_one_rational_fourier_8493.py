from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 8471
assert d["appliedSourceCuspCyclotomicSpanning"]["receipt8471"]["exit"] == 0
assert (p / "paper-verification-8471-console.exit").read_text().strip() == "0"
assert (r/'Tools/cusp-cyclotomic-spanning-20261026-685/canonical-evidence-8471.json').exists()
key = "appliedSourceGammaOneRationalFourier"
assert key not in d
digests = {'source-fricke-cyclotomic-analytic-transport-5-scratch-receipt.json': 'EA8A4E86BF2EBC0C77970E18CB0F48BC533023901809C3D38FD0B77D0C4474EA', 'source-gamma-one-cyclotomic-conjugation-13-scratch-receipt.json': '5F58C8E699F7DF819D1238C44212F1760649FA0E5642AB2BDAF1C58B032B8C6F', 'source-gamma-one-rational-cusp-span-4-scratch-receipt.json': '0CAC2FADB6D241264A529DA1B438678735411E074B567CFDD60DAE9D7EE4BBFF'}

for name, digest in digests.items():
    assert sha(p / name) == digest
certs = [json.loads((p / name).read_text(encoding="utf-8")) for name in digests]
mods = [m for z in certs for m in z["modules"]]
queries = [q for z in certs for q in z["queries"]]
theorems = [q for z in certs for q in z["theoremRegistrations"]]
defs = [q for z in certs for q in z["constructionRegistrations"]]
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (22, 22, 63, 58, 5)
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
archive_rel='Tools/gamma-one-rational-fourier-20261026-692'
evidence=[p/'gamma-one-rational-fourier-promotion-route-692.json']
evidence += [p/n for n in ['SourceFrickeCyclotomicAnalyticTransportAudit5.exit', 'SourceFrickeCyclotomicAnalyticTransportAudit5.lean', 'SourceFrickeCyclotomicAnalyticTransportAudit5.log', 'SourceFrickeCyclotomicAnalyticTransportDependencyAudit5.exit', 'SourceFrickeCyclotomicAnalyticTransportDependencyAudit5.lean', 'SourceFrickeCyclotomicAnalyticTransportDependencyAudit5.log', 'SourceGammaOneCyclotomicConjugationAudit13.exit', 'SourceGammaOneCyclotomicConjugationAudit13.lean', 'SourceGammaOneCyclotomicConjugationAudit13.log', 'SourceGammaOneCyclotomicConjugationDependencyAudit13.exit', 'SourceGammaOneCyclotomicConjugationDependencyAudit13.lean', 'SourceGammaOneCyclotomicConjugationDependencyAudit13.log', 'SourceGammaOneCyclotomicConjugationDependencyAudit13V2.exit', 'SourceGammaOneCyclotomicConjugationDependencyAudit13V2.lean', 'SourceGammaOneCyclotomicConjugationDependencyAudit13V2.log', 'SourceGammaOneRationalCuspSpanAudit4.exit', 'SourceGammaOneRationalCuspSpanAudit4.lean', 'SourceGammaOneRationalCuspSpanAudit4.log', 'SourceGammaOneRationalCuspSpanDependencyAudit4.exit', 'SourceGammaOneRationalCuspSpanDependencyAudit4.lean', 'SourceGammaOneRationalCuspSpanDependencyAudit4.log', 'fetch_gamma_one_cyclotomic_transport_inputs_686.py', 'fricke-cyclotomic-analytic-transport-route-687.json', 'gamma-one-cyclotomic-conjugation-route-688.json', 'gamma-one-cyclotomic-transport-reuse-assessment-686.json', 'gamma-one-rational-cusp-span-route-689.json', 'make_fricke_cyclotomic_analytic_transport_audit_687.py', 'make_gamma_one_cyclotomic_conjugation_audit_688.py', 'make_gamma_one_cyclotomic_conjugation_receipt_688.py', 'make_gamma_one_rational_cusp_span_audit_689.py', 'prepare_cyclotomic_elliptic_divisibility_688.py', 'prepare_fricke_cyclotomic_analytic_transport_audit_687.py', 'prepare_gamma_one_cyclotomic_conjugation_audit_688.py', 'prepare_gamma_one_cyclotomic_conjugation_dependency_688b.py', 'prepare_gamma_one_rational_cusp_span_audit_689.py', 'record_fricke_cyclotomic_analytic_transport_687.py', 'record_gamma_one_cyclotomic_conjugation_688.py', 'record_gamma_one_cyclotomic_transport_review_686.py', 'record_gamma_one_rational_cusp_span_689.py', 'source-fricke-cyclotomic-analytic-transport-5-audit-config.json', 'source-fricke-cyclotomic-analytic-transport-5-scratch-receipt.json', 'source-gamma-one-cyclotomic-conjugation-13-audit-config-v2.json', 'source-gamma-one-cyclotomic-conjugation-13-audit-config.json', 'source-gamma-one-cyclotomic-conjugation-13-scratch-receipt.json', 'source-gamma-one-rational-cusp-span-4-audit-config.json', 'source-gamma-one-rational-cusp-span-4-scratch-receipt.json']]
for folder in ['fricke-laurent-field-conjugation-api-687a', 'cyclotomic-cancellation-api-failed-688a', 'cyclotomic-transport-pretrim-688b', 'gamma-one-trace-api-failed-689a', 'gamma-one-cyclotomic-transport-inputs-reuse-686']:
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
supplemental_review_path=r/archive_rel/'gamma-one-rational-fourier-promotion-route-692.json'

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
reuse_path = r / "Tools/source-gamma-one-rational-fourier.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt8471"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> arithmetic realization of original finite Gamma1 Hecke characters -> actual Picard/H1, full/parabolic, transpose and diamond comparison retaining the original homogeneous coefficient endomorphism -> actual differential/cusp comparison -> rational Fourier spanning of actual Gamma1 cusp forms.'
discharged = 'The actual cyclotomic torsion-index permutation preserves the original Laurent generated field and j-integrality; the existing holomorphic representative theorem constructs actual conjugate Fricke fractions. Integral modular lifts and original Gamma1 translations prove modular covariance and preserve level invariance. Laurent order transports all-cusp vanishing. Holomorphic division in the original fraction algebra preserves both elliptic divisibility conditions through actual j and j-1728 coordinates. The exact cusp characterization constructs another actual cusp form of the same weight and level, and rational Eisenstein/discriminant cancellation identifies its literal width-one coefficients with their cyclotomic conjugates. The original coefficient field is finite Galois over Q. Actual trace sums have rational Fourier coefficients, and the pinned Mathlib trace-dual basis reconstructs each original-image generator. The already proved original-image spanning theorem therefore yields rational Fourier spanning of the full Gamma1 weight-two cusp-form space at every nonzero level. General weights retain the explicit source balance k+4a+6b=12m; weight two uses a=b=m=1.'
boundary = 'Rational Fourier spanning is proved, but bounded denominators for the original integral-ratio function field remain. Arbitrary Gamma1 cusp differential realization and the converse regular-differential construction remain. The actual Picard/H1, full/parabolic, transpose and diamond comparison must identify original finite homogeneous-coefficient Hecke characters with geometric characters. Frobenius/inertia, arithmetic realization of those characters, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain. No unrestricted odd-weight weight-lowering claim is made, and the all-weight arithmetic goal is unchanged. Complex semisimplicity, finite characters, Witt coefficients and universal deformation rings do not supply a characteristic-zero lift or point. 16/20; DUB-17--20 OPEN.'
status = 'The rational Fourier spanning chain passes 89 exhaustive scratch theorem checks and 63 public axiom queries across 22 modules, with sixteen linters per module and zero diagnostics. Three declaration-value audits verify 87 required dependencies. Production aggregate, focused audit and sequential foundation/paper verification of the 8,493-module scope are pending.'
route = 'The renewed selected-file search is recorded in Dubon Reuse Search 2026-10-26.md. Reuse the original Laurent integral representative instead of the external rational-at-infinity and recursive Fourier-division packages. Use the proved SL2 reduction lift and local Gamma1 translation lift for covariance, the original cusp characterization for analytic reconstruction, and exact Laurent germs for coefficients. Construct conjugates only for the original-image generating set, which already spans; defer the unnecessary stronger conjugation theorem for every cyclotomic-coefficient form. Native trace-dual basis reconstruction replaces the external Dedekind-independence and matrix-invertibility proof. No external full import closure was built or certified. Failed audit/helper evidence and retained failed source variants are preserved. Only audited mathematical sources are promoted and only imports are qualified. Pins, proof limits, source contract and all twenty acceptance gates are unchanged.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Actual Gamma1 rational Fourier spanning (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 8,471-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
corrections = []
count = sum(z['exhaustiveTheorems'] for z in certs)
assert count == 89

docpaths = list(dict.fromkeys(r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]))
for f in docpaths:
    assert "\n\n" in f.read_text(encoding="utf-8")
readmes = [(r.parent / "README.md", "Current Project 83 status ("), (repo / "README.md", "Project 83 has an ")]
for f, prefix in readmes:
    assert sum(line.startswith(prefix) for line in f.read_text(encoding="utf-8").splitlines()) == 1
arch = r / "Dubon Architecture.md"
edge = '  CUSPCYCLOTOMIC8471["Actual cusp-image twist stability, full fixed-field descent and cyclotomic Fourier spanning of Gamma1 weight-two cusp forms proved. Rational descent over Q, bounded denominators, differential realization/converse, Picard/H1/diamond, original all-weight association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourceGammaOneRationalFourierProductionAudit8493.lean',p/'source-gamma-one-rational-fourier-8493-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production8493.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/cusp-cyclotomic-spanning-20261026-685'
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
    "productionModules": 8493, "modules": newmods, "queries": queries,
    "theoremRegistrations": theorems, "constructionRegistrations": defs,
    "sourceHashes": {mapping[t.stem]: sha(t) for t, _ in pending}, "scratchCertificates": certs,
    "exactDependency": dependency, "assumptionsDischarged": discharged, "stillOpen": boundary,
    "status": status, "rootPinsChanged": False, "proofLimitsChanged": False,
    "promotionChanges": 'Only scratch imports are qualified. Every final audited statement, proof body and comment is preserved. The original cyclotomic field, actual Fricke fractions, integral modular lifts, original E4/E6/Delta factors, same-level cusp forms, literal Fourier coefficients and native trace-dual reconstruction remain explicit. No source contract is weakened.',
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
arch.write_text(arch.read_text(encoding='utf-8').replace(edge,'  CUSPCYCLOTOMIC8471["Actual cusp-image twist stability and cyclotomic Fourier spanning (DUB-17/18)"] --> GAMMAONERATIONAL8493\n  GAMMAONERATIONAL8493["Actual same-level cyclotomic cusp conjugates and rational Fourier spanning of Gamma1 weight-two cusp forms proved. Bounded denominators, differential realization/converse, Picard/H1/diamond, original all-weight association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'),encoding='utf-8')



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Actual Gamma1 rational Fourier spanning - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-gamma-one-rational-fourier.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub('  logInfo m!".*"\n', '  logInfo m!"SOURCE GAMMA ONE RATIONAL FOURIER AUDIT PASS: {count} theorems including private/generated declarations. Actual same-level cyclotomic cusp conjugates and rational Fourier spanning of Gamma1 weight-two cusp forms are proved. Bounded denominators, differential realization and arithmetic comparison remain; 16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourceGammaOneRationalFourierProductionAudit8493.lean").write_text(out, encoding="utf-8")
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
    target = p / (source.stem + "Production8493.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
(p / "source-gamma-one-rational-fourier-8493-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 8493, "increment": 22, "queries": 63,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
