from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 8548
assert d["appliedSourceGammaOneRegularCusp"]["receipt8548"]["exit"] == 0
assert (p / "paper-verification-8548-console.exit").read_text().strip() == "0"
assert (r/'Tools/gamma-one-regular-cusp-20261026-704/canonical-evidence-8548.json').exists()
key = "appliedSourceGammaOnePeriodCharts"
assert key not in d
digests = {'source-gamma-one-period-germ-1-scratch-receipt.json': '69518C1D18858B6E6DBFC11B5FE2F939FFAEDE31100388FADAEB39379D22EDBE', 'source-gamma-one-analytic-residues-3-scratch-receipt.json': '4AF476A43C86FA83B7570B5BD31E8BE82E27C782D100B7EBCCFB72FF93756918', 'source-gamma-one-unramified-charts-2-scratch-receipt.json': '724D35DA2C0ED9ED8975FEF2E366A18910FDB36B310E0C4BBDFF301FD6206165'}

for name, digest in digests.items():
    assert sha(p / name) == digest
certs = [json.loads((p / name).read_text(encoding="utf-8")) for name in digests]
mods = [m for z in certs for m in z["modules"]]
queries = [q for z in certs for q in z["queries"]]
theorems = [q for z in certs for q in z["theoremRegistrations"]]
defs = [q for z in certs for q in z["constructionRegistrations"]]
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (6, 6, 19, 18, 1)
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
archive_rel='Tools/gamma-one-period-charts-20261026-709'
evidence=[p/'gamma-one-period-charts-promotion-route-709.json']
evidence += [p/n for n in ['SourceGammaOneAnalyticResiduesAudit3.exit', 'SourceGammaOneAnalyticResiduesAudit3.lean', 'SourceGammaOneAnalyticResiduesAudit3.log', 'SourceGammaOneAnalyticResiduesDependencyAudit3.exit', 'SourceGammaOneAnalyticResiduesDependencyAudit3.lean', 'SourceGammaOneAnalyticResiduesDependencyAudit3.log', 'SourceGammaOneAnalyticResiduesScratchOwnership706.exit', 'SourceGammaOneAnalyticResiduesScratchOwnership706.lean', 'SourceGammaOneAnalyticResiduesScratchOwnership706.log', 'SourceGammaOnePeriodGermAudit1.exit', 'SourceGammaOnePeriodGermAudit1.lean', 'SourceGammaOnePeriodGermAudit1.log', 'SourceGammaOnePeriodGermDependencyAudit1.exit', 'SourceGammaOnePeriodGermDependencyAudit1.lean', 'SourceGammaOnePeriodGermDependencyAudit1.log', 'SourceGammaOnePeriodGermScratchOwnership705.exit', 'SourceGammaOnePeriodGermScratchOwnership705.lean', 'SourceGammaOnePeriodGermScratchOwnership705.log', 'SourceGammaOneUnramifiedChartsAudit2.exit', 'SourceGammaOneUnramifiedChartsAudit2.lean', 'SourceGammaOneUnramifiedChartsAudit2.log', 'SourceGammaOneUnramifiedChartsDependencyAudit2.exit', 'SourceGammaOneUnramifiedChartsDependencyAudit2.lean', 'SourceGammaOneUnramifiedChartsDependencyAudit2.log', 'SourceGammaOneUnramifiedChartsScratchOwnership707.exit', 'SourceGammaOneUnramifiedChartsScratchOwnership707.lean', 'SourceGammaOneUnramifiedChartsScratchOwnership707.log', 'consumers707.txt', 'download_gamma_one_ramification_core_708.py', 'download_gamma_one_ramification_followup_708.py', 'download_gamma_one_ramification_inputs_708.py', 'foundation707-console.log', 'foundation707-retry-console.log', 'gamma-one-analytic-residues-audit-route-706.json', 'gamma-one-analytic-residues-route-706.json', 'gamma-one-analytic-residues-scratch-ownership-706.json', 'gamma-one-period-germ-audit-route-705.json', 'gamma-one-period-germ-route-705.json', 'gamma-one-period-germ-scratch-ownership-705.json', 'gamma-one-unramified-charts-audit-route-707.json', 'gamma-one-unramified-charts-route-707.json', 'gamma-one-unramified-charts-scratch-ownership-707.json', 'modules707.json', 'paper707-console.log', 'paper707-retry-console.log', 'prepare_gamma_one_period_germ_audit_705.py', 'record707.py', 'record_gamma_one_analytic_residues_706.py', 'record_gamma_one_period_germ_705.py', 'record_gamma_one_unramified_charts_707.py', 'register707.py', 'registrations707.json', 'section707.txt', 'source-gamma-one-analytic-residues-3-audit-config.json', 'source-gamma-one-analytic-residues-3-scratch-receipt.json', 'source-gamma-one-period-germ-1-audit-config.json', 'source-gamma-one-period-germ-1-scratch-receipt.json', 'source-gamma-one-unramified-charts-2-audit-config.json', 'source-gamma-one-unramified-charts-2-scratch-receipt.json', 'status707.txt', 'update707.py']]
for folder in ['gamma-one-ramification-core-reuse-708', 'gamma-one-analytic-evaluation-failed-706a', 'gamma-one-period-germ-failed-705a', 'gamma-one-period-germ-failed-705b', 'gamma-one-ramification-isolation-failed-707a', 'gamma-one-unramified-charts-failed-707b', 'gamma-one-unramified-charts-failed-707c', 'gamma-one-period-charts-preparation-failed-709a']:
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
supplemental_review_path=r/archive_rel/'gamma-one-period-charts-promotion-route-709.json'

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
reuse_path = r / "Tools/source-gamma-one-period-charts.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt8548"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> arithmetic realization of original finite Gamma1 Hecke characters -> Picard/H1, full/parabolic, transpose and diamond comparison retaining the original homogeneous coefficient endomorphism -> actual differential/cusp period normalization and original analytic place charts.'
discharged = 'The actual Fourier-normalized regular-differential/cusp equivalence has the exact analytic integrand 2*pi*i times the cusp form, for every original regular differential including zero. Actual residue evaluation on the original Gamma field equals the regular analytic limit and the meromorphic normal form, with exact normalized-place orders and punctured-germ equality. At each unramified analytic center, one radius and the actual uniformizer construct an injective local chart with normalized orders for every original field element. Exact j-multiplicity and isolated E4/E6 zeros derive unramifiedness away from those zeros; no chart, residue comparison, order model or differential-coordinate witness is supplied.'
boundary = 'Elliptic-center ramified descent, finite/cusp place exhaustion and global Gamma1 charts remain, followed by actual global period and Hecke/diamond/Picard/H1 comparison. These local charts do not close the full arithmetic realization of original finite homogeneous-coefficient characters. Coefficient-field transport, Frobenius/inertia, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain. The full all-weight arithmetic goal is unchanged. Complex semisimplicity, finite characters, Witt coefficients and universal deformation rings do not supply a characteristic-zero lift or point. 16/20; DUB-17--20 OPEN.'
status = 'The exact actual differential integrand, algebraic/analytic residue comparison and unramified charts pass 31 exhaustive scratch theorem checks and 19 public axiom queries across 6 modules, with sixteen linters per module and zero diagnostics. Three declaration-value audits verify 43 required dependencies. Production aggregate, focused audit and sequential foundation/paper verification of the 8,554-module scope are pending.'
route = 'Reuse the proved Fourier equivalence and quotient normalization to identify the analytic integrand. Reuse generic rational residue evaluation, finite-coordinate closed residue fields and native meromorphic normal form. Reuse the exact j-multiplicity theorem and generic inverse-function parameter theorem for actual unramified charts. Selected pinned FLT ramification files are archived for route assessment; they do not supply a locally certified import closure. Only audited mathematical sources are promoted and only imports are qualified. Failed variants and audit/helper evidence remain preserved. Pins, proof limits, frozen paper and all twenty acceptance gates are unchanged.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Actual Gamma1 period normalization and local charts (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 8,548-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
corrections = []
count = sum(z['exhaustiveTheorems'] for z in certs)
assert count == 31

docpaths = list(dict.fromkeys(r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]))
for f in docpaths:
    assert "\n\n" in f.read_text(encoding="utf-8")
readmes = [(r.parent / "README.md", "Current Project 83 status ("), (repo / "README.md", "Project 83 has an ")]
for f, prefix in readmes:
    assert sum(line.startswith(prefix) for line in f.read_text(encoding="utf-8").splitlines()) == 1
arch = r / "Dubon Architecture.md"
edge = '  GAMMAONEREGULAR8548["Actual complex Gamma1 regular-differential/cusp linear equivalence with exact Fourier normalization proved. Original Hecke/diamond/Picard/H1, all-weight arithmetic association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourceGammaOnePeriodChartsProductionAudit8554.lean',p/'source-gamma-one-period-charts-8554-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production8554.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/gamma-one-regular-cusp-20261026-704'
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
    "productionModules": 8554, "modules": newmods, "queries": queries,
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
arch.write_text(arch.read_text(encoding='utf-8').replace(edge,'  GAMMAONEREGULAR8548["Actual complex Gamma1 regular-differential/cusp equivalence with exact Fourier normalization (DUB-17/18)"] --> GAMMAONEPERIOD8554\n  GAMMAONEPERIOD8554["Exact differential integrand, actual residue comparison and unramified local charts proved. Elliptic/global charts, period/Hecke/diamond/Picard/H1, all-weight arithmetic association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'),encoding='utf-8')



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Actual Gamma1 period normalization and local charts - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-gamma-one-period-charts.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub('  logInfo m!".*"\n', '  logInfo m!"SOURCE GAMMA ONE PERIOD CHARTS AUDIT PASS: {count} theorems including private/generated declarations. The exact actual Gamma1 differential integrand, residue comparison and unramified charts are proved. Elliptic and global chart/period obligations remain. Original Hecke/diamond/Picard/H1 arithmetic comparison remains; 16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourceGammaOnePeriodChartsProductionAudit8554.lean").write_text(out, encoding="utf-8")
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
    target = p / (source.stem + "Production8554.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
(p / "source-gamma-one-period-charts-8554-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 8554, "increment": 6, "queries": 19,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
