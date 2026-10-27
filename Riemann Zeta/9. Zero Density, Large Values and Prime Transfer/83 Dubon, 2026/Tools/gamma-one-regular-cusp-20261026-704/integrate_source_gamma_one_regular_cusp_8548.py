from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 8522
assert d["appliedSourceGammaOneIntegralDifferential"]["receipt8522"]["exit"] == 0
assert (p / "paper-verification-8522b-console.exit").read_text().strip() == "0"
assert (r/'Tools/gamma-one-integral-differential-20261026-699/canonical-evidence-8522.json').exists()
key = "appliedSourceGammaOneRegularCusp"
assert key not in d
digests = {'source-gamma-one-local-holomorphy-12-scratch-receipt.json': 'FA3FD70DE720E7EE3293CDC2A682101E803B4903C25540687D4B8DEC4C1DF38F', 'source-gamma-one-cusp-vanishing-10-scratch-receipt.json': 'FB9076F6E4AB51929ED0D62B4B587B1957ED227357C5DAA8668716744DF1AE4E', 'source-gamma-one-fourier-converse-2-scratch-receipt.json': '3502062B579879A237F3DA6B6E8043899B99BF8F18357E6FB37251CC611C7811', 'source-gamma-one-linear-comparison-2-scratch-receipt.json': '5A715A3A21FD94D009218A675A76EA77F6304041FC2FBDB8D2DB24AD94265F50'}

for name, digest in digests.items():
    assert sha(p / name) == digest
certs = [json.loads((p / name).read_text(encoding="utf-8")) for name in digests]
mods = [m for z in certs for m in z["modules"]]
queries = [q for z in certs for q in z["queries"]]
theorems = [q for z in certs for q in z["theoremRegistrations"]]
defs = [q for z in certs for q in z["constructionRegistrations"]]
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (26, 26, 80, 69, 11)
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
archive_rel='Tools/gamma-one-regular-cusp-20261026-704'
evidence=[p/'gamma-one-regular-cusp-promotion-route-704.json']
evidence += [p/n for n in ['SourceGammaOneAnalyticDifferentialRegularity-pretrim-700e.exit', 'SourceGammaOneAnalyticDifferentialRegularity-pretrim-700e.log', 'SourceGammaOneAnalyticJOrders-pretrim-700e.exit', 'SourceGammaOneAnalyticJOrders-pretrim-700e.log', 'SourceGammaOneAnalyticPlaces-pretrim-700e.exit', 'SourceGammaOneAnalyticPlaces-pretrim-700e.log', 'SourceGammaOneCuspVanishingAudit10.exit', 'SourceGammaOneCuspVanishingAudit10.lean', 'SourceGammaOneCuspVanishingAudit10.log', 'SourceGammaOneCuspVanishingDependencyAudit10.exit', 'SourceGammaOneCuspVanishingDependencyAudit10.lean', 'SourceGammaOneCuspVanishingDependencyAudit10.log', 'SourceGammaOneCuspVanishingScratchOwnership701.exit', 'SourceGammaOneCuspVanishingScratchOwnership701.lean', 'SourceGammaOneCuspVanishingScratchOwnership701.log', 'SourceGammaOneFourierConverseAudit2.exit', 'SourceGammaOneFourierConverseAudit2.lean', 'SourceGammaOneFourierConverseAudit2.log', 'SourceGammaOneFourierConverseDependencyAudit2.exit', 'SourceGammaOneFourierConverseDependencyAudit2.lean', 'SourceGammaOneFourierConverseDependencyAudit2.log', 'SourceGammaOneFourierConverseScratchOwnership702.exit', 'SourceGammaOneFourierConverseScratchOwnership702.lean', 'SourceGammaOneFourierConverseScratchOwnership702.log', 'SourceGammaOneHolomorphicDifferentials-pretrim-700e.exit', 'SourceGammaOneHolomorphicDifferentials-pretrim-700e.log', 'SourceGammaOneLinearComparisonAudit2.exit', 'SourceGammaOneLinearComparisonAudit2.lean', 'SourceGammaOneLinearComparisonAudit2.log', 'SourceGammaOneLinearComparisonDependencyAudit2.exit', 'SourceGammaOneLinearComparisonDependencyAudit2.lean', 'SourceGammaOneLinearComparisonDependencyAudit2.log', 'SourceGammaOneLinearComparisonScratchOwnership703.exit', 'SourceGammaOneLinearComparisonScratchOwnership703.lean', 'SourceGammaOneLinearComparisonScratchOwnership703.log', 'SourceGammaOneLocalHolomorphyAudit12.exit', 'SourceGammaOneLocalHolomorphyAudit12.lean', 'SourceGammaOneLocalHolomorphyAudit12.log', 'SourceGammaOneLocalHolomorphyDependencyAudit12.exit', 'SourceGammaOneLocalHolomorphyDependencyAudit12.lean', 'SourceGammaOneLocalHolomorphyDependencyAudit12.log', 'SourceGammaOneLocalHolomorphyScratchOwnership700.exit', 'SourceGammaOneLocalHolomorphyScratchOwnership700.lean', 'SourceGammaOneLocalHolomorphyScratchOwnership700.log', 'consumers700.txt', 'gamma-one-cusp-vanishing-audit-route-701.json', 'gamma-one-cusp-vanishing-route-701.json', 'gamma-one-cusp-vanishing-scratch-ownership-701.json', 'gamma-one-fourier-converse-audit-route-702.json', 'gamma-one-fourier-converse-route-702.json', 'gamma-one-fourier-converse-scratch-ownership-702.json', 'gamma-one-linear-comparison-audit-route-703.json', 'gamma-one-linear-comparison-route-703.json', 'gamma-one-linear-comparison-scratch-ownership-703.json', 'gamma-one-local-converse-route-700.json', 'gamma-one-local-holomorphy-audit-route-700.json', 'gamma-one-local-holomorphy-scratch-ownership-700.json', 'gamma-one-local-holomorphy-selected-scope-700e.json', 'modules700.json', 'prepare_gamma_one_cusp_vanishing_audit_701.py', 'prepare_gamma_one_fourier_converse_audit_702.py', 'prepare_gamma_one_holomorphic_realization_700.py', 'prepare_gamma_one_linear_comparison_audit_703.py', 'prepare_gamma_one_local_holomorphy_audit_700.py', 'prepare_gamma_one_local_holomorphy_receipt_700.py', 'prepare_gamma_one_local_orders_700.py', 'prepare_gamma_one_local_realization_700.py', 'record700.py', 'record_gamma_one_cusp_vanishing_701.py', 'record_gamma_one_fourier_converse_702.py', 'record_gamma_one_linear_comparison_703.py', 'record_gamma_one_local_holomorphy_700.py', 'register700.py', 'registrations700.json', 'section700.txt', 'source-gamma-one-cusp-vanishing-10-audit-config.json', 'source-gamma-one-cusp-vanishing-10-scratch-receipt.json', 'source-gamma-one-fourier-converse-2-audit-config.json', 'source-gamma-one-fourier-converse-2-scratch-receipt.json', 'source-gamma-one-linear-comparison-2-audit-config.json', 'source-gamma-one-linear-comparison-2-scratch-receipt.json', 'source-gamma-one-local-holomorphy-12-audit-config.json', 'source-gamma-one-local-holomorphy-12-scratch-receipt.json', 'status700.txt', 'update700.py']]
for folder in ['gamma-one-converse-core-reuse-698', 'gamma-one-analytic-order-failed-700a', 'gamma-one-analytic-places-failed-700b', 'gamma-one-cusp-derivative-failed-701c', 'gamma-one-cusp-order-failed-701b', 'gamma-one-fourier-realization-failed-702a', 'gamma-one-fourier-realization-failed-702b', 'gamma-one-j-orders-failed-700d', 'gamma-one-linear-equivalence-warning-703g', 'gamma-one-linear-expansion-failed-703a', 'gamma-one-linear-expansion-failed-703b', 'gamma-one-linear-expansion-failed-703c', 'gamma-one-linear-expansion-failed-703d', 'gamma-one-linear-expansion-failed-703e', 'gamma-one-linear-expansion-failed-703f', 'gamma-one-local-holomorphy-pretrim-700e', 'gamma-one-regular-cusp-order-failed-701d', 'gamma-one-regular-orders-failed-700c', 'gamma-one-translated-cusp-failed-701a']:
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
supplemental_review_path=r/archive_rel/'gamma-one-regular-cusp-promotion-route-704.json'

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
reuse_path = r / "Tools/source-gamma-one-regular-cusp.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt8522"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> arithmetic realization of original finite Gamma1 Hecke characters -> actual Picard/H1, full/parabolic, transpose and diamond comparison retaining the original homogeneous coefficient endomorphism -> actual regular-differential/cusp equivalence with literal Fourier normalization.'
discharged = 'The actual original complex Gamma1 regular differential space is now linearly equivalent to native weight-two cusp forms, with exact equality of their literal Fourier expansions. Actual modular quotient germs define normalized finite and cusp places. Original regularity and exact j-derivative orders give finite holomorphy and positive order at every cusp, deriving all analytic and decay hypotheses. The existing modular q-Euler identity removes the precise 2*pi*i factor. The proved differential spanning theorem covers every regular differential. Both Fourier realization directions and injectivity identify the actual linear ranges; no dimension formula, matching-series witness or cusp-form-existence assumption is supplied.'
boundary = 'The actual Picard/H1, full/parabolic, transpose and diamond comparison must still identify original finite homogeneous-coefficient Hecke characters with geometric characters. Exact analytic period normalization and compatibility with the original Hecke/diamond operators remain. Coefficient-field transport is still required wherever used by the arithmetic comparison. Frobenius/inertia, arithmetic realization of those characters, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain. The full all-weight arithmetic goal is unchanged. Complex semisimplicity, finite characters, Witt coefficients and universal deformation rings do not supply a characteristic-zero lift or point. 16/20; DUB-17--20 OPEN.'
status = 'The actual complex Gamma1 regular-differential/cusp equivalence passes 132 exhaustive scratch theorem checks and 80 public axiom queries across 26 modules, with sixteen linters per module and zero diagnostics. Four declaration-value audits verify 116 required dependencies. Production aggregate, focused audit and sequential foundation/paper verification of the 8,548-module scope are pending.'
route = 'The renewed selected-file search is recorded in Dubon Reuse Search 2026-10-26.md. Reuse actual modular ratios, normalized place construction, exact local differential orders, native removable singularities, the existing j-derivative and q-Euler identities, original integral Fourier spanning and differential expansion injectivity. This gives the required complex equivalence without a new global Gamma1 ramification classification, cusp-width dictionary, numerical degree bound, period-germ framework or dimension formula. The external comparison files were inspected at the pinned commit; their full import closure was not built or certified. Only audited mathematical sources are promoted and only imports are qualified. Failed variants and audit/helper evidence remain preserved. Pins, proof limits, frozen source and all twenty acceptance gates are unchanged.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Actual Gamma1 regular-differential/cusp equivalence (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 8,522-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
corrections = []
count = sum(z['exhaustiveTheorems'] for z in certs)
assert count == 132

docpaths = list(dict.fromkeys(r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]))
for f in docpaths:
    assert "\n\n" in f.read_text(encoding="utf-8")
readmes = [(r.parent / "README.md", "Current Project 83 status ("), (repo / "README.md", "Project 83 has an ")]
for f, prefix in readmes:
    assert sum(line.startswith(prefix) for line in f.read_text(encoding="utf-8").splitlines()) == 1
arch = r / "Dubon Architecture.md"
edge = '  GAMMAONEINTEGRAL8522["Actual integral Fourier spanning and coefficient-field-valued cusp to regular differential realization proved. Converse, Picard/H1/diamond, original all-weight association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourceGammaOneRegularCuspProductionAudit8548.lean',p/'source-gamma-one-regular-cusp-8548-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production8548.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/gamma-one-integral-differential-20261026-699'
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
    "productionModules": 8548, "modules": newmods, "queries": queries,
    "theoremRegistrations": theorems, "constructionRegistrations": defs,
    "sourceHashes": {mapping[t.stem]: sha(t) for t, _ in pending}, "scratchCertificates": certs,
    "exactDependency": dependency, "assumptionsDischarged": discharged, "stillOpen": boundary,
    "status": status, "rootPinsChanged": False, "proofLimitsChanged": False,
    "promotionChanges": 'Only scratch imports are qualified. All final audited statements, proof bodies and comments remain identical. The original function field, actual regular differentials, native cusp forms, literal Fourier series and exact complex normalization are retained. No source contract is weakened.',
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
arch.write_text(arch.read_text(encoding='utf-8').replace(edge,'  GAMMAONEINTEGRAL8522["Actual integral Fourier spanning and coefficient-field-valued cusp to regular differential realization (DUB-17/18)"] --> GAMMAONEREGULAR8548\n  GAMMAONEREGULAR8548["Actual complex Gamma1 regular-differential/cusp linear equivalence with exact Fourier normalization proved. Original Hecke/diamond/Picard/H1, all-weight arithmetic association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'),encoding='utf-8')



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Actual Gamma1 regular-differential/cusp equivalence - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-gamma-one-regular-cusp.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub('  logInfo m!".*"\n', '  logInfo m!"SOURCE GAMMA ONE REGULAR CUSP AUDIT PASS: {count} theorems including private/generated declarations. The actual complex Gamma1 regular-differential/cusp linear equivalence and literal Fourier identity are proved. Original Hecke/diamond/Picard/H1 arithmetic comparison remains; 16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourceGammaOneRegularCuspProductionAudit8548.lean").write_text(out, encoding="utf-8")
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
    target = p / (source.stem + "Production8548.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
(p / "source-gamma-one-regular-cusp-8548-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 8548, "increment": 26, "queries": 80,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
