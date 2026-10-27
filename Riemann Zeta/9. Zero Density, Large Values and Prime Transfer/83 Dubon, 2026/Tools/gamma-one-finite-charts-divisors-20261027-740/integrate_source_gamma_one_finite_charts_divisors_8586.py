from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 8576
assert d["appliedSourceGammaOneAnalyticOrbits"]["receipt8576"]["exit"] == 0
assert (p / "paper-verification-8576-console.exit").read_text().strip() == "0"
assert (r/'Tools/gamma-one-analytic-orbits-20261027-730/canonical-evidence-8576.json').exists()
key = "appliedSourceGammaOneFiniteChartsDivisors"
assert key not in d
digests = {'source-gamma-one-exact-ramification-1-scratch-receipt.json': 'D538B51BD02993D8333DC989DCEED95AF9A699A50B5A21014A8A5B445645E0B3', 'source-gamma-one-ramified-regular-1b-scratch-receipt.json': '9F93976A802868C297AE919E66CCF5AB1F2EFA6BECC002013F7C66965838E6D6', 'source-gamma-one-ramified-chart-orders-1b-scratch-receipt.json': '45F9005E2039F1FADD28CDC047729D1B40163BBC090BCE5D5AE995D3AFE84035', 'source-gamma-one-finite-chart-parameters-1-scratch-receipt.json': '97484611A1C2F818629C37CE7D2711BF99E99A6EEAEE8F7F39541CBB2B2B13C2', 'source-gamma-one-divisor-moving-1-scratch-receipt.json': 'A88376EC334AB34572E6E20E05245BAE932A7E0FAEFC77F87480E28E18AEA1B7'}

for name, digest in digests.items():
    assert sha(p / name) == digest
certs = [json.loads((p / name).read_text(encoding="utf-8")) for name in digests]
mods = [m for z in certs for m in z["modules"]]
queries = [q for z in certs for q in z["queries"]]
theorems = [q for z in certs for q in z["theoremRegistrations"]]
defs = [q for z in certs for q in z["constructionRegistrations"]]
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (10, 10, 22, 21, 1)
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
archive_rel='Tools/gamma-one-finite-charts-divisors-20261027-740'
evidence=[p/'gamma-one-finite-charts-divisors-promotion-route-740.json']
evidence += [p/n for n in ['SourceGammaOneAnalyticDivisorMoving.exit', 'SourceGammaOneAnalyticDivisorMoving.lean', 'SourceGammaOneAnalyticDivisorMoving.log', 'SourceGammaOneDivisorMovingAudit1.exit', 'SourceGammaOneDivisorMovingAudit1.lean', 'SourceGammaOneDivisorMovingAudit1.log', 'SourceGammaOneDivisorMovingDependencyAudit1.exit', 'SourceGammaOneDivisorMovingDependencyAudit1.lean', 'SourceGammaOneDivisorMovingDependencyAudit1.log', 'SourceGammaOneDivisorMovingScratchOwnership738.exit', 'SourceGammaOneDivisorMovingScratchOwnership738.lean', 'SourceGammaOneDivisorMovingScratchOwnership738.log', 'SourceGammaOneEllipticFibers.exit', 'SourceGammaOneEllipticFibers.lean', 'SourceGammaOneEllipticFibers.log', 'SourceGammaOneExactRamification.exit', 'SourceGammaOneExactRamification.lean', 'SourceGammaOneExactRamification.log', 'SourceGammaOneExactRamificationAudit1.exit', 'SourceGammaOneExactRamificationAudit1.lean', 'SourceGammaOneExactRamificationAudit1.log', 'SourceGammaOneExactRamificationDependencyAudit1.exit', 'SourceGammaOneExactRamificationDependencyAudit1.lean', 'SourceGammaOneExactRamificationDependencyAudit1.log', 'SourceGammaOneExactRamificationScratchOwnership731.exit', 'SourceGammaOneExactRamificationScratchOwnership731.lean', 'SourceGammaOneExactRamificationScratchOwnership731.log', 'SourceGammaOneFiniteChartParameters.exit', 'SourceGammaOneFiniteChartParameters.lean', 'SourceGammaOneFiniteChartParameters.log', 'SourceGammaOneFiniteChartParametersAudit1.exit', 'SourceGammaOneFiniteChartParametersAudit1.lean', 'SourceGammaOneFiniteChartParametersAudit1.log', 'SourceGammaOneFiniteChartParametersDependencyAudit1.exit', 'SourceGammaOneFiniteChartParametersDependencyAudit1.lean', 'SourceGammaOneFiniteChartParametersDependencyAudit1.log', 'SourceGammaOneFiniteChartParametersScratchOwnership735.exit', 'SourceGammaOneFiniteChartParametersScratchOwnership735.lean', 'SourceGammaOneFiniteChartParametersScratchOwnership735.log', 'SourceGammaOneNearbyOrders.exit', 'SourceGammaOneNearbyOrders.lean', 'SourceGammaOneNearbyOrders.log', 'SourceGammaOnePrescribedPlaceOrders.exit', 'SourceGammaOnePrescribedPlaceOrders.lean', 'SourceGammaOnePrescribedPlaceOrders.log', 'SourceGammaOneRamifiedChartOrders.exit', 'SourceGammaOneRamifiedChartOrders.lean', 'SourceGammaOneRamifiedChartOrders.log', 'SourceGammaOneRamifiedChartOrdersAudit1.exit', 'SourceGammaOneRamifiedChartOrdersAudit1.lean', 'SourceGammaOneRamifiedChartOrdersAudit1.log', 'SourceGammaOneRamifiedChartOrdersAudit1b.exit', 'SourceGammaOneRamifiedChartOrdersAudit1b.lean', 'SourceGammaOneRamifiedChartOrdersAudit1b.log', 'SourceGammaOneRamifiedChartOrdersDependencyAudit1.exit', 'SourceGammaOneRamifiedChartOrdersDependencyAudit1.lean', 'SourceGammaOneRamifiedChartOrdersDependencyAudit1.log', 'SourceGammaOneRamifiedChartOrdersDependencyAudit1b.exit', 'SourceGammaOneRamifiedChartOrdersDependencyAudit1b.lean', 'SourceGammaOneRamifiedChartOrdersDependencyAudit1b.log', 'SourceGammaOneRamifiedChartOrdersScratchOwnership734.exit', 'SourceGammaOneRamifiedChartOrdersScratchOwnership734.lean', 'SourceGammaOneRamifiedChartOrdersScratchOwnership734.log', 'SourceGammaOneRamifiedChartOrdersScratchOwnership734b.exit', 'SourceGammaOneRamifiedChartOrdersScratchOwnership734b.lean', 'SourceGammaOneRamifiedChartOrdersScratchOwnership734b.log', 'SourceGammaOneRamifiedMeromorphicOrder.exit', 'SourceGammaOneRamifiedMeromorphicOrder.lean', 'SourceGammaOneRamifiedMeromorphicOrder.log', 'SourceGammaOneRamifiedRegularAudit1.exit', 'SourceGammaOneRamifiedRegularAudit1.lean', 'SourceGammaOneRamifiedRegularAudit1.log', 'SourceGammaOneRamifiedRegularAudit1b.exit', 'SourceGammaOneRamifiedRegularAudit1b.lean', 'SourceGammaOneRamifiedRegularAudit1b.log', 'SourceGammaOneRamifiedRegularDependencyAudit1.lean', 'SourceGammaOneRamifiedRegularDependencyAudit1b.exit', 'SourceGammaOneRamifiedRegularDependencyAudit1b.lean', 'SourceGammaOneRamifiedRegularDependencyAudit1b.log', 'SourceGammaOneRamifiedRegularOrder.exit', 'SourceGammaOneRamifiedRegularOrder.lean', 'SourceGammaOneRamifiedRegularOrder.log', 'SourceGammaOneRamifiedRegularParameter.exit', 'SourceGammaOneRamifiedRegularParameter.lean', 'SourceGammaOneRamifiedRegularParameter.log', 'SourceGammaOneRamifiedRegularScratchOwnership733b.exit', 'SourceGammaOneRamifiedRegularScratchOwnership733b.lean', 'SourceGammaOneRamifiedRegularScratchOwnership733b.log', 'compare_reuse_heads_741.py', 'consumers734.txt', 'download_gamma_one_global_period_inputs_736c.py', 'download_gamma_one_global_period_route_736.py', 'download_gamma_one_global_period_route_736b.py', 'download_gamma_one_period_alternative_739.py', 'download_gamma_one_period_alternative_739b.py', 'foundation734-console.log', 'gamma-one-divisor-moving-audit-route-738.json', 'gamma-one-divisor-moving-route-738.json', 'gamma-one-exact-ramification-audit-route-731.json', 'gamma-one-exact-ramification-route-731.json', 'gamma-one-finite-chart-parameters-audit-route-735.json', 'gamma-one-finite-chart-parameters-route-735.json', 'gamma-one-ramified-chart-orders-audit-route-734.json', 'gamma-one-ramified-chart-orders-audit-route-734b.json', 'gamma-one-ramified-chart-orders-route-734.json', 'gamma-one-ramified-regular-audit-route-733.json', 'gamma-one-ramified-regular-route-733.json', 'inspect_reuse_primary_741c.py', 'inspect_reuse_subtrees_741b.py', 'inspect_reuse_updates_741.py', 'modules734.json', 'paper734-console.log', 'prepare_gamma_one_divisor_moving_738.py', 'prepare_gamma_one_divisor_moving_audit_738.py', 'prepare_gamma_one_exact_ramification_audit_731.py', 'prepare_gamma_one_finite_chart_parameters_audit_735.py', 'prepare_gamma_one_ramified_chart_orders_734.py', 'prepare_gamma_one_ramified_chart_orders_audit_734.py', 'prepare_gamma_one_ramified_finite_charts_promotion_8584.py', 'prepare_gamma_one_ramified_regular_733.py', 'prepare_gamma_one_ramified_regular_audit_733.py', 'record734.py', 'record_gamma_one_divisor_moving_738.py', 'record_gamma_one_exact_ramification_731.py', 'record_gamma_one_finite_chart_parameters_735.py', 'record_gamma_one_ramified_chart_orders_734.py', 'record_gamma_one_ramified_chart_orders_734b.py', 'record_gamma_one_ramified_regular_733.py', 'record_gamma_one_ramified_regular_733b.py', 'record_reuse_refresh_741.py', 'refresh_reuse_heads_741.py', 'registrations734.json', 'section734.txt', 'source-gamma-one-divisor-moving-1-audit-config.json', 'source-gamma-one-divisor-moving-1-scratch-receipt.json', 'source-gamma-one-exact-ramification-1-audit-config.json', 'source-gamma-one-exact-ramification-1-scratch-receipt.json', 'source-gamma-one-finite-chart-parameters-1-audit-config.json', 'source-gamma-one-finite-chart-parameters-1-scratch-receipt.json', 'source-gamma-one-ramified-chart-orders-1-audit-config.json', 'source-gamma-one-ramified-chart-orders-1-scratch-receipt.json', 'source-gamma-one-ramified-chart-orders-1b-audit-config.json', 'source-gamma-one-ramified-chart-orders-1b-scratch-receipt.json', 'source-gamma-one-ramified-regular-1-audit-config.json', 'source-gamma-one-ramified-regular-1b-audit-config.json', 'source-gamma-one-ramified-regular-1b-scratch-receipt.json', 'status734.txt']]
for folder in ['gamma-one-divisor-moving-failed-738a', 'gamma-one-divisor-moving-failed-738b', 'gamma-one-divisor-moving-failed-738c', 'gamma-one-divisor-moving-failed-738d', 'gamma-one-divisor-moving-failed-738e', 'gamma-one-exact-ramification-failed-731a', 'gamma-one-exact-ramification-failed-731b', 'gamma-one-finite-chart-parameters-failed-735a', 'gamma-one-global-period-download-failed-736a', 'gamma-one-global-period-route-reuse-736', 'gamma-one-period-alternative-reuse-739', 'gamma-one-ramified-audit-wrapper-failed-733b', 'gamma-one-ramified-chart-orders-dependency-refresh-734b', 'gamma-one-ramified-regular-failed-733a', 'reuse-head-refresh-741']:
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
supplemental_review_path=r/archive_rel/'gamma-one-finite-charts-divisors-promotion-route-740.json'

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
reuse_path = r / "Tools/source-gamma-one-finite-charts-divisors.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt8576"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> arithmetic realization of original finite Gamma1 Hecke characters -> Picard/H1, full/parabolic, transpose and diamond comparison retaining the original homogeneous coefficient endomorphism -> actual differential and period geometry -> exact normalized charts at all finite places, including elliptic points, and analytic representatives of all original degree-zero divisor classes.'
discharged = 'The actual coordinate extension degree equals the index of Gamma1 enlarged by the central negative identity. Equality of finite-fiber sums with the termwise bounds proves twice the actual analytic ramification equals the actual enlarged stabilizer cardinality. Actual places are constant on centered-coordinate power fibers, so regular residue values descend analytically with their exact normalized orders. Inversion extends the result to all meromorphic functions. One disk works for every function and every nearby point. Every actual place where j is regular has an injective uniformizer-normalized chart, exact function orders, regular analyticity and coordinate differences of order one. Every nonzero level and elliptic center is retained. No ramification equality, normalized finite chart, analytic descent or function-order comparison remains a supplied hypothesis. Actual finite-place indicators prescribe arbitrary orders without an approximation input. Subtracting the resulting principal divisor moves every actual divisor class to a finite analytic divisor; degree-zero classes have analytic coefficient sum zero.'
boundary = 'Actual global period and Hecke/diamond/Picard/H1 comparison remain. Cusp/global-chart construction and a possible modular-period alternative are being compared; the pinned alternative still requires genuine period surjectivity, reciprocity, meromorphic field realization and cusp-order control. The present results do not close arithmetic realization of original finite homogeneous-coefficient characters. Coefficient-field transport, Frobenius/inertia, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain. The full all-weight arithmetic goal is unchanged. Complex semisimplicity, finite characters, Witt coefficients and universal deformation rings do not supply a characteristic-zero lift or point. 16/20; DUB-17--20 OPEN.'
status = 'Actual Gamma1 exact elliptic ramification and normalized charts at every finite j-place and analytic divisor representatives pass 48 exhaustive scratch theorem checks and 22 public axiom queries across ten modules, with sixteen linters per module and zero diagnostics. Five declaration-value audits verify 55 required dependencies. Production aggregate, focused audit and sequential foundation/paper verification of the 8,586-module scope are pending.'
route = 'Selected pinned Apache-2.0 elliptic and ramified-chart arguments are adapted using already proved local exact fiber counts, native power descent, local root branches, rational residue inversion and the existing inverse-function parameter theorem. Actual curve geometry and finite-place indicators supply the required divisor-moving argument. This avoids rebuilding those foundations. The renewed search also identifies an alternative principal-divisor proof using nonzero cusp limits; its full dependencies are under assessment in the preserved scope-736 and scope-739 research and are not claimed proved. The live 27 October refresh of seven repositories and the inspected new Mathlib, OpenAI and zeta-lab changes are recorded in Dubon Reuse Refresh 2026-10-27.md; none of the inspected updates closes the missing arithmetic or global-period obligation. Only audited mathematical sources are promoted, with imports qualified and proof bodies unchanged. The unused-argument correction, completed predecessor checks and every failure are preserved. Pins, proof limits, frozen paper and all twenty acceptance gates are unchanged.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Actual Gamma1 finite charts and analytic divisor representatives (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 8,576-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
corrections = []
count = sum(z['exhaustiveTheorems'] for z in certs)
assert count == 48

docpaths = list(dict.fromkeys(r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]))
for f in docpaths:
    assert "\n\n" in f.read_text(encoding="utf-8")
readmes = [(r.parent / "README.md", "Current Project 83 status ("), (repo / "README.md", "Project 83 has an ")]
for f, prefix in readmes:
    assert sum(line.startswith(prefix) for line in f.read_text(encoding="utf-8").splitlines()) == 1
arch = r / "Dubon Architecture.md"
edge = '  GAMMAONEORBITS8576["Actual Gamma1 finite-place exhaustion, exact analytic-place orbits and finite j-fiber bijections proved. Exact elliptic ramification/global charts, period/Hecke/diamond/Picard/H1, all-weight arithmetic association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourceGammaOneFiniteChartsDivisorsProductionAudit8586.lean',p/'source-gamma-one-finite-charts-divisors-8586-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production8586.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/gamma-one-analytic-orbits-20261027-730'
registered = {row['path'] for row in c['files']}
for priorFile in priorArchive.iterdir():
    rel = priorFile.relative_to(r).as_posix()
    if priorFile.is_file() and rel not in registered:
        c['files'].append({'path': rel, 'role': 'Tools'})

reportSource = p / 'reuse-head-refresh-741/Dubon Reuse Refresh 2026-10-27.md'
assert sha(reportSource) == '0492A53D656A52E89B93B5EB506066901BAB9507AF71E81608B394B1A338C34D'
reportTarget = r / reportSource.name
assert not reportTarget.exists()

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
reportTarget.write_bytes(reportSource.read_bytes())
c['files'].append({'path': reportTarget.name, 'role': 'root'})
cp.write_text(json.dumps(c, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
d[key] = {"recordedUTC": datetime.now(timezone.utc).isoformat(), "date": dateLabel,
    "productionModules": 8586, "modules": newmods, "queries": queries,
    "theoremRegistrations": theorems, "constructionRegistrations": defs,
    "sourceHashes": {mapping[t.stem]: sha(t) for t, _ in pending}, "scratchCertificates": certs,
    "exactDependency": dependency, "assumptionsDischarged": discharged, "stillOpen": boundary,
    "status": status, "rootPinsChanged": False, "proofLimitsChanged": False,
    "promotionChanges": 'Only scratch imports are qualified. All final audited statements, proof bodies and comments remain identical. The actual original integral-ratio field, all nonzero levels, elliptic stabilizers, residue values and normalized place orders are retained.',
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
arch.write_text(arch.read_text(encoding='utf-8').replace(edge,'  GAMMAONEORBITS8576["Actual Gamma1 finite-place exhaustion, exact analytic-place orbits and finite j-fiber bijections (DUB-17/18)"] --> GAMMAONEFINITE8586\n  GAMMAONEFINITE8586["Exact elliptic ramification, normalized finite charts and analytic representatives of every divisor class proved. Global periods, Hecke/diamond/Picard/H1, all-weight arithmetic association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'),encoding='utf-8')



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Actual Gamma1 finite charts and analytic divisor representatives - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-gamma-one-finite-charts-divisors.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub('  logInfo m!".*"\n', '  logInfo m!"SOURCE GAMMA ONE FINITE CHARTS AND DIVISORS AUDIT PASS: {count} theorems including private/generated declarations. Exact elliptic ramification, normalized finite charts and analytic representatives of every divisor class are proved. Global periods and original Hecke/diamond/Picard/H1 arithmetic comparison remain; 16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourceGammaOneFiniteChartsDivisorsProductionAudit8586.lean").write_text(out, encoding="utf-8")
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
    target = p / (source.stem + "Production8586.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
(p / "source-gamma-one-finite-charts-divisors-8586-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 8586, "increment": 10, "queries": 22,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
