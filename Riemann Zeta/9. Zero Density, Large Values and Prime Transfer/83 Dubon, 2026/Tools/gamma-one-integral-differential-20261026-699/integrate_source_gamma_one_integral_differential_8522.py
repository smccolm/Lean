from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 8493
assert d["appliedSourceGammaOneRationalFourier"]["receipt8493"]["exit"] == 0
assert (p / "paper-verification-8493-console.exit").read_text().strip() == "0"
assert (r/'Tools/gamma-one-rational-fourier-20261026-692/canonical-evidence-8493.json').exists()
key = "appliedSourceGammaOneIntegralDifferential"
assert key not in d
digests = {'source-gamma-one-integral-cusp-span-23-scratch-receipt.json': 'C18E5C8AF9E00AA65BFE91DC91F31025F8B1227985D4FBBB70CCD63B6C7A1E80', 'source-gamma-one-cusp-differential-realization-6-scratch-receipt.json': '8801725A8FAEC671A45FD3F1B9573CCE05C55EDF3780B8C1BB46BA55F1946C5D'}

for name, digest in digests.items():
    assert sha(p / name) == digest
certs = [json.loads((p / name).read_text(encoding="utf-8")) for name in digests]
mods = [m for z in certs for m in z["modules"]]
queries = [q for z in certs for q in z["queries"]]
theorems = [q for z in certs for q in z["theoremRegistrations"]]
defs = [q for z in certs for q in z["constructionRegistrations"]]
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (29, 29, 68, 63, 5)
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
archive_rel='Tools/gamma-one-integral-differential-20261026-699'
evidence=[p/'gamma-one-integral-differential-promotion-route-699.json']
evidence += [p/n for n in ['SourceGammaOneCuspDifferentialRealizationAudit6.exit', 'SourceGammaOneCuspDifferentialRealizationAudit6.lean', 'SourceGammaOneCuspDifferentialRealizationAudit6.log', 'SourceGammaOneCuspDifferentialRealizationDependencyAudit6.exit', 'SourceGammaOneCuspDifferentialRealizationDependencyAudit6.lean', 'SourceGammaOneCuspDifferentialRealizationDependencyAudit6.log', 'SourceGammaOneCuspDifferentialScratchOwnership697.exit', 'SourceGammaOneCuspDifferentialScratchOwnership697.lean', 'SourceGammaOneCuspDifferentialScratchOwnership697.log', 'SourceGammaOneIntegralCuspScratchOwnership696.exit', 'SourceGammaOneIntegralCuspScratchOwnership696.lean', 'SourceGammaOneIntegralCuspScratchOwnership696.log', 'SourceGammaOneIntegralCuspScratchOwnership696V2.exit', 'SourceGammaOneIntegralCuspScratchOwnership696V2.lean', 'SourceGammaOneIntegralCuspScratchOwnership696V2.log', 'SourceGammaOneIntegralCuspSpanAudit23.exit', 'SourceGammaOneIntegralCuspSpanAudit23.lean', 'SourceGammaOneIntegralCuspSpanAudit23.log', 'SourceGammaOneIntegralCuspSpanAudit23V2.exit', 'SourceGammaOneIntegralCuspSpanAudit23V2.lean', 'SourceGammaOneIntegralCuspSpanAudit23V2.log', 'SourceGammaOneIntegralCuspSpanDependencyAudit23V2.exit', 'SourceGammaOneIntegralCuspSpanDependencyAudit23V2.lean', 'SourceGammaOneIntegralCuspSpanDependencyAudit23V2.log', 'bounded-denominator-reuse-assessment-690.json', 'consumers691.txt', 'fetch_bounded_denominator_inputs_690b.py', 'fetch_gamma_one_bounded_denominator_core_690.py', 'gamma-one-cusp-differential-realization-audit-route-697.json', 'gamma-one-cusp-differential-scratch-ownership-697.json', 'gamma-one-differential-realization-route-697.json', 'gamma-one-integral-cusp-span-route-696.json', 'integral-cusp-linter-repair-696b.json', 'integral-cusp-ownership-encoding-repair-696c.json', 'integral-cusp-scratch-ownership-696.json', 'integral-cusp-selected-scope-696.json', 'laurent-denominator-reuse-route-695.json', 'modules691.json', 'prepare_bounded_denominator_inputs_690b.py', 'prepare_gamma_one_differential_realization_audit_697.py', 'prepare_integral_cusp_audit_696.py', 'prepare_integral_cusp_scope_696.py', 'record691.py', 'record_bounded_denominator_reuse_review_690.py', 'record_gamma_one_differential_realization_697.py', 'record_gamma_one_integral_cusp_span_696.py', 'record_laurent_denominator_route_695.py', 'record_shorter_denominator_routes_693_694.py', 'register691.py', 'registrations691.json', 'restore_frozen_span_module_695.py', 'restore_frozen_span_module_695b.py', 'scratch-name-collision-restoration-695.json', 'scratch-name-collision-restoration-verification-695.json', 'section691.txt', 'shorter-denominator-route-693.json', 'shorter-denominator-route-694.json', 'source-gamma-one-cusp-differential-realization-6-audit-config.json', 'source-gamma-one-cusp-differential-realization-6-scratch-receipt.json', 'source-gamma-one-integral-cusp-span-23-audit-config.json', 'source-gamma-one-integral-cusp-span-23-scratch-receipt.json', 'status691.txt']]
for folder in ['gamma-one-bounded-denominator-core-reuse-690', 'bounded-denominator-series-inputs-reuse-690b', 'deferred-power-series-route-696', 'integral-cusp-linter-failure-696b', 'integer-j-normalization-failed-697a', 'gamma-one-differential-realization-failed-697b', 'scratch-name-collision-695']:
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
supplemental_review_path=r/archive_rel/'gamma-one-integral-differential-promotion-route-699.json'

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
reuse_path = r / "Tools/source-gamma-one-integral-differential.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt8493"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> arithmetic realization of original finite Gamma1 Hecke characters -> actual Picard/H1, full/parabolic, transpose and diamond comparison retaining the original homogeneous coefficient endomorphism -> actual differential/cusp comparison -> integral Fourier spanning and regular differential realization of actual Gamma1 weight-two cusp forms.'
discharged = 'Every rational Fourier coefficient sequence of an actual Gamma1 cusp form satisfying the source weight balance has a single nonzero integer denominator. The proof derives the original cyclotomic Fricke-field membership and monic equation, bounds the actual torsion Weierstrass numerators, descends a nonzero bounded fraction by the native field trace, and uses native Laurent-series integral closure. Exact integral Eisenstein units and the discriminant cancel the weight factors. Rational spanning therefore yields integral Fourier spanning of the entire actual Gamma1 weight-two cusp space. The existing complex j-derivative identity descends to an integral identity with a proved nonzero integer normalization. Actual same-weight integral modular ratios then construct the differential coefficient for every integral cusp generator. Coefficientwise span descent realizes every cusp form whose coefficients lie in the given field embedding as an actual differential on the original integral-ratio Gamma1 function field. Over an algebraically closed coefficient field the already proved local regularity criterion makes this differential regular. No bounded-denominator, field-membership, monic-relation or differential-existence assumption remains in these consumers.'
boundary = 'The converse from an actual regular Gamma1 differential to an actual cusp form remains. The actual Picard/H1, full/parabolic, transpose and diamond comparison must identify original finite homogeneous-coefficient Hecke characters with geometric characters. Frobenius/inertia, arithmetic realization of those characters, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain. General-weight denominator and spanning statements retain the explicit balance k+4a+6b=12m; weight two derives it with a=b=m=1. The full all-weight arithmetic goal is unchanged. Complex semisimplicity, finite characters, Witt coefficients and universal deformation rings do not supply a characteristic-zero lift or point. 16/20; DUB-17--20 OPEN.'
status = 'The integral Fourier spanning and forward differential realization chain passes 91 exhaustive scratch theorem checks and 68 public axiom queries across 29 modules, with sixteen linters per module and zero diagnostics. Two declaration-value audits verify 87 required dependencies. Production aggregate, focused audit and sequential foundation/paper verification of the 8,522-module scope are pending.'
route = 'The renewed selected-file search is recorded in Dubon Reuse Search 2026-10-26.md. Reuse the original Laurent field, native normality under localization, native trace and the proved rational cusp span. This avoids the unused power-series-only route and the external recursive coefficient division. Construct the differential directly as a multiple of D(j); reuse the existing exact complex derivative formula, integral-ratio field and regularity criterion, avoiding a new differential-expansion framework. The pinned external arguments supplied finite denominator scaling and the geometric comparison route; their full import closure was not built or certified. Only audited mathematical sources are promoted and only imports are qualified. Failed variants and audit/helper evidence remain preserved. Pins, proof limits, frozen source and all twenty acceptance gates are unchanged.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Actual Gamma1 integral Fourier spanning and differential realization (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 8,493-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
corrections = []
count = sum(z['exhaustiveTheorems'] for z in certs)
assert count == 91

docpaths = list(dict.fromkeys(r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]))
for f in docpaths:
    assert "\n\n" in f.read_text(encoding="utf-8")
readmes = [(r.parent / "README.md", "Current Project 83 status ("), (repo / "README.md", "Project 83 has an ")]
for f, prefix in readmes:
    assert sum(line.startswith(prefix) for line in f.read_text(encoding="utf-8").splitlines()) == 1
arch = r / "Dubon Architecture.md"
edge = '  GAMMAONERATIONAL8493["Actual same-level cyclotomic cusp conjugates and rational Fourier spanning of Gamma1 weight-two cusp forms proved. Bounded denominators, differential realization/converse, Picard/H1/diamond, original all-weight association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourceGammaOneIntegralDifferentialProductionAudit8522.lean',p/'source-gamma-one-integral-differential-8522-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production8522.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/gamma-one-rational-fourier-20261026-692'
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
    "productionModules": 8522, "modules": newmods, "queries": queries,
    "theoremRegistrations": theorems, "constructionRegistrations": defs,
    "sourceHashes": {mapping[t.stem]: sha(t) for t, _ in pending}, "scratchCertificates": certs,
    "exactDependency": dependency, "assumptionsDischarged": discharged, "stillOpen": boundary,
    "status": status, "rootPinsChanged": False, "proofLimitsChanged": False,
    "promotionChanges": 'Only scratch imports are qualified. All final audited statements, proof bodies and comments remain identical. Original Fricke and integral-ratio fields, exact Laurent and Fourier coefficients, integer denominators, actual cusp forms and actual regular differentials are retained. No source contract is weakened.',
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
arch.write_text(arch.read_text(encoding='utf-8').replace(edge,'  GAMMAONERATIONAL8493["Actual same-level cyclotomic cusp conjugates and rational Fourier spanning (DUB-17/18)"] --> GAMMAONEINTEGRAL8522\n  GAMMAONEINTEGRAL8522["Actual integral Fourier spanning and coefficient-field-valued cusp to regular differential realization proved. Converse, Picard/H1/diamond, original all-weight association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'),encoding='utf-8')



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Actual Gamma1 integral Fourier spanning and differential realization - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-gamma-one-integral-differential.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub('  logInfo m!".*"\n', '  logInfo m!"SOURCE GAMMA ONE INTEGRAL DIFFERENTIAL AUDIT PASS: {count} theorems including private/generated declarations. Actual integral Fourier spanning and forward regular differential realization are proved. Converse and arithmetic comparison remain; 16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourceGammaOneIntegralDifferentialProductionAudit8522.lean").write_text(out, encoding="utf-8")
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
    target = p / (source.stem + "Production8522.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
(p / "source-gamma-one-integral-differential-8522-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 8522, "increment": 29, "queries": 68,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
