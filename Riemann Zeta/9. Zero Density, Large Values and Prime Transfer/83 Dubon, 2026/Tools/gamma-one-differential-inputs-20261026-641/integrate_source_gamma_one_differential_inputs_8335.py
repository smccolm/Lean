from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 8316
assert d["appliedSourceGammaOneArithmeticGeometry"]["receipt8316"]["exit"] == 0
assert (p / "paper-verification-8316-console.exit").read_text().strip() == "0"
assert (r/'Tools/gamma-one-arithmetic-geometry-20261026-626/canonical-evidence-8316.json').exists()
key = "appliedSourceGammaOneDifferentialInputs"
assert key not in d
digests = {'source-gamma-one-geometric-subgroup-1-scratch-receipt.json': 'B20BC28E86B9674390D7360751DFE680BDC7BFCE6FA787B36B5461A3F76AE0C3', 'source-gamma-one-geometric-cohomology-1-scratch-receipt.json': 'E2EDC0A0CF457E4C9F0F70FF482D77550117A037C82ABC7AF16EA8C7033DC47A', 'source-gamma-one-hecke-coefficient-1-scratch-receipt.json': 'B35B8DCB281A6050421DBA5BB8EB81AFA7710E592D034899DC30FDDC371887F8', 'source-gamma-one-curve-geometry-2-scratch-receipt.json': '378499A246B5EA00C058B7E6E7008486CB53FF706B6920E3A4DF71AFC8F27979', 'source-gamma-one-scalar-extension-1-scratch-receipt.json': '39F1F0BAE1C276431397DE4757293D6AB7FA2634C8CCD2D72E80F9EB94E04021', 'source-gamma-one-field-modular-ratio-2-scratch-receipt.json': '9149584D53B8B74568CAED0F9D0E2BEE3F819570A05CF30DF0789CDAB9DE04F5', 'source-gamma-one-differential-finite-integral-5-scratch-receipt.json': '447878A306BA2A05157FF70C19B8B05455C9B679CC428947714118E7EF484F18', 'source-gamma-one-differential-cusp-integral-6-scratch-receipt.json': '0404466E30FD58C7EEE6272B9F223E799034FAC35EC07ED888BE14518F759652'}

for name, digest in digests.items():
    assert sha(p / name) == digest
certs = [json.loads((p / name).read_text(encoding="utf-8")) for name in digests]
mods = [m for z in certs for m in z["modules"]]
queries = [q for z in certs for q in z["queries"]]
theorems = [q for z in certs for q in z["theoremRegistrations"]]
defs = [q for z in certs for q in z["constructionRegistrations"]]
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (19, 19, 85, 73, 12)
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
archive_rel='Tools/gamma-one-differential-inputs-20261026-641'
evidence=[p/'gamma-one-differential-inputs-promotion-route-641.json']
evidence += [p/n for n in ['SourceGammaOneCurveGeometryAudit2.exit', 'SourceGammaOneCurveGeometryAudit2.lean', 'SourceGammaOneCurveGeometryAudit2.log', 'SourceGammaOneCurveGeometryDependencyAudit2.exit', 'SourceGammaOneCurveGeometryDependencyAudit2.lean', 'SourceGammaOneCurveGeometryDependencyAudit2.log', 'SourceGammaOneDifferentialCuspIntegralAudit6.exit', 'SourceGammaOneDifferentialCuspIntegralAudit6.lean', 'SourceGammaOneDifferentialCuspIntegralAudit6.log', 'SourceGammaOneDifferentialCuspIntegralDependencyAudit6.exit', 'SourceGammaOneDifferentialCuspIntegralDependencyAudit6.lean', 'SourceGammaOneDifferentialCuspIntegralDependencyAudit6.log', 'SourceGammaOneDifferentialFiniteIntegralAudit5.exit', 'SourceGammaOneDifferentialFiniteIntegralAudit5.lean', 'SourceGammaOneDifferentialFiniteIntegralAudit5.log', 'SourceGammaOneDifferentialFiniteIntegralDependencyAudit5.exit', 'SourceGammaOneDifferentialFiniteIntegralDependencyAudit5.lean', 'SourceGammaOneDifferentialFiniteIntegralDependencyAudit5.log', 'SourceGammaOneFieldModularRatioAudit2.exit', 'SourceGammaOneFieldModularRatioAudit2.lean', 'SourceGammaOneFieldModularRatioAudit2.log', 'SourceGammaOneFieldModularRatioDependencyAudit2.exit', 'SourceGammaOneFieldModularRatioDependencyAudit2.lean', 'SourceGammaOneFieldModularRatioDependencyAudit2.log', 'SourceGammaOneGeometricCohomologyAudit1.exit', 'SourceGammaOneGeometricCohomologyAudit1.lean', 'SourceGammaOneGeometricCohomologyAudit1.log', 'SourceGammaOneGeometricCohomologyDependencyAudit1.exit', 'SourceGammaOneGeometricCohomologyDependencyAudit1.lean', 'SourceGammaOneGeometricCohomologyDependencyAudit1.log', 'SourceGammaOneGeometricSubgroupAudit1.exit', 'SourceGammaOneGeometricSubgroupAudit1.lean', 'SourceGammaOneGeometricSubgroupAudit1.log', 'SourceGammaOneGeometricSubgroupDependencyAudit1.exit', 'SourceGammaOneGeometricSubgroupDependencyAudit1.lean', 'SourceGammaOneGeometricSubgroupDependencyAudit1.log', 'SourceGammaOneHeckeCoefficientAudit1.exit', 'SourceGammaOneHeckeCoefficientAudit1.lean', 'SourceGammaOneHeckeCoefficientAudit1.log', 'SourceGammaOneHeckeCoefficientDependencyAudit1.exit', 'SourceGammaOneHeckeCoefficientDependencyAudit1.lean', 'SourceGammaOneHeckeCoefficientDependencyAudit1.log', 'SourceGammaOneScalarExtensionAudit1.exit', 'SourceGammaOneScalarExtensionAudit1.lean', 'SourceGammaOneScalarExtensionAudit1.log', 'SourceGammaOneScalarExtensionDependencyAudit1.exit', 'SourceGammaOneScalarExtensionDependencyAudit1.lean', 'SourceGammaOneScalarExtensionDependencyAudit1.log', 'consumers627.txt', 'consumers634.txt', 'consumers638.txt', 'fetch_gamma1_cusp_integral_639.py', 'fetch_gamma1_differential_inputs_633.py', 'fetch_gamma1_differential_prerequisites_635.py', 'fetch_gamma1_qeuler_637.py', 'gamma1-actual-curve-differential-route-632.json', 'gamma1-cusp-integral-reuse-assessment-639.json', 'gamma1-differential-cusp-integral-route-640.json', 'gamma1-differential-finite-integral-route-638.json', 'gamma1-differential-input-reuse-assessment-633.json', 'gamma1-differential-prerequisite-reuse-assessment-635.json', 'gamma1-field-modular-ratio-route-636.json', 'gamma1-geometric-cohomology-route-629.json', 'gamma1-hecke-coefficient-factor-route-631.json', 'gamma1-qeuler-reuse-assessment-637.json', 'gamma1-scalar-extension-route-634.json', 'gamma1-upper-geometric-correspondence-route-627.json', 'modules627.json', 'modules634.json', 'modules638.json', 'prepare_gamma_one_curve_geometry_audit_632.py', 'prepare_gamma_one_curve_geometry_scope_632.py', 'prepare_gamma_one_differential_cusp_integral_audit_640.py', 'prepare_gamma_one_differential_finite_integral_audit_638.py', 'prepare_gamma_one_field_modular_ratio_audit_636.py', 'prepare_gamma_one_geometric_cohomology_audit_629.py', 'prepare_gamma_one_geometric_cohomology_scope_629.py', 'prepare_gamma_one_geometric_subgroup_audit_627.py', 'prepare_gamma_one_geometric_subgroup_scope_627.py', 'prepare_gamma_one_hecke_coefficient_audit_631.py', 'prepare_gamma_one_hecke_coefficient_scope_631.py', 'prepare_gamma_one_scalar_extension_audit_634.py', 'record627.py', 'record634.py', 'record638.py', 'record_gamma_one_curve_geometry_632.py', 'record_gamma_one_differential_cusp_integral_640.py', 'record_gamma_one_differential_finite_integral_638.py', 'record_gamma_one_field_modular_ratio_636.py', 'record_gamma_one_geometric_cohomology_629.py', 'record_gamma_one_geometric_subgroup_627.py', 'record_gamma_one_hecke_coefficient_631.py', 'record_gamma_one_scalar_extension_634.py', 'register627.py', 'register634.py', 'register638.py', 'registrations627.json', 'registrations634.json', 'registrations638.json', 'section627.txt', 'section634.txt', 'section638.txt', 'source-gamma-one-curve-geometry-2-audit-config.json', 'source-gamma-one-curve-geometry-2-scratch-receipt.json', 'source-gamma-one-differential-cusp-integral-6-audit-config.json', 'source-gamma-one-differential-cusp-integral-6-scratch-receipt.json', 'source-gamma-one-differential-finite-integral-5-audit-config.json', 'source-gamma-one-differential-finite-integral-5-scratch-receipt.json', 'source-gamma-one-field-modular-ratio-2-audit-config.json', 'source-gamma-one-field-modular-ratio-2-scratch-receipt.json', 'source-gamma-one-geometric-cohomology-1-audit-config.json', 'source-gamma-one-geometric-cohomology-1-scratch-receipt.json', 'source-gamma-one-geometric-subgroup-1-audit-config.json', 'source-gamma-one-geometric-subgroup-1-scratch-receipt.json', 'source-gamma-one-hecke-coefficient-1-audit-config.json', 'source-gamma-one-hecke-coefficient-1-scratch-receipt.json', 'source-gamma-one-scalar-extension-1-audit-config.json', 'source-gamma-one-scalar-extension-1-scratch-receipt.json', 'status627.txt', 'status634.txt', 'status638.txt']]
for folder in ['gamma1-differential-input-reuse-633', 'gamma1-differential-prerequisite-reuse-635', 'gamma1-qeuler-reuse-637', 'gamma1-cusp-integral-reuse-639', 'gamma1-inverse-j-640-before-explicit-coefficient-rewrite']:
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
supplemental_review_path=r/archive_rel/'gamma-one-differential-inputs-promotion-route-641.json'

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
reuse_path = r / "Tools/source-gamma-one-differential-inputs.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt8316"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero Galois association -> arithmetic realization of original finite Gamma1 Hecke characters -> actual Picard/H1, full/parabolic and diamond comparison retaining the original homogeneous coefficient endomorphism -> exact geometric H1 correspondence, actual curve and regular differential/cusp comparison.'
discharged = 'The actual upper and geometric Hecke subgroups are explicitly isomorphic with the original conjugation and analytic matrix action. Native H1 pullback/trace gives exactly the original finite Hecke operator, including its homogeneous coefficient endomorphism, and this action factors on either side of the geometric operator. Existing finite-coordinate curve results establish local differential generators, canonical divisors and injective expansions for the actual Gamma1 and Hecke fields. Literal scalar extension equals the complex integral-ratio field; every element has a same-weight complex modular quotient with nonzero denominator. This does not assert the reverse membership of arbitrary complex modular quotients. Native analytic differentiation and the existing level-one dimension theorem construct a nonzero q-Euler normalization scalar. For an actual weight-two cusp form f and Y*qEuler(j)=qExpansion(f), the finite expression Y^6*j^4*(j-1728)^3 is integral over C[j]; for positive M with Gamma(M) contained in the group, the cusp expression Y^(2M)*j^(M+1)*(j-1728)^M is integral over C[1/j]. Existing modular norms and level-one polynomial reduction, plus native cusp exponential decay, prove both integral equations without assuming them.'
boundary = 'The valuation deduction of regularity, algebraic differential realization and converse cusp construction remain. The actual Picard/H1, full/parabolic, transpose and diamond comparison must still identify the original finite homogeneous-coefficient Hecke characters with geometric characters. Frobenius/inertia, arithmetic realization of these characters, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain required. Neither complex semisimplicity, finite characters, Witt coefficients nor a universal deformation ring supplies a characteristic-zero lift or point. 16/20; DUB-17--20 OPEN.'
status = 'The actual Gamma1 H1 and differential-input chain passes 138 exhaustive scratch checks and 85 explicit public axiom queries across 19 modules, with sixteen linters per module and zero diagnostics. Eight declaration-value audits verify 136 required dependencies. Production aggregate, focused audit and sequential foundation/paper verification of the 8,335-module scope are pending.'
route = 'The renewed search is recorded in Dubon Reuse Search 2026-10-26.md; deeper fixed-revision differential inputs are archived here. Reuse native H1 composition and original coset sums, existing finite-coordinate curve/canonical theorems, literal Laurent scalar extension and native modular quotient operations. Use the existing bounded derivative and level-one weight-14 dimension theorem rather than a new Ramanujan system. Cubing permits reuse of the existing weight-12 modular orbit polynomial for the inverse-j bound; no second interpolation construction is needed. Native cusp decay constructs f^(2M)*E4^3/Delta. Preserve the constructed nonzero scalar instead of proving an unnecessary exact normalization. A restriction-unfolding recursion-depth diagnostic is preserved; explicit coefficient identities resolve it with unchanged limits. No external project was built or imported; root pins and all twenty gates are unchanged.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Actual Gamma1 cohomology and differential inputs (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 8,316-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
corrections = []
count = sum(z['exhaustiveTheorems'] for z in certs)
assert count == 138

docpaths = list(dict.fromkeys(r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]))
for f in docpaths:
    assert "\n\n" in f.read_text(encoding="utf-8")
readmes = [(r.parent / "README.md", "Current Project 83 status ("), (repo / "README.md", "Project 83 has an ")]
for f, prefix in readmes:
    assert sum(line.startswith(prefix) for line in f.read_text(encoding="utf-8").splitlines()) == 1
arch = r / "Dubon Architecture.md"
edge = '  GAMMAONEFIELDS8316["Actual Gamma1 fields, finite maps, Picard Hecke and arithmetic equivariance proved. Original homogeneous-coefficient H1/diamond comparison, Frobenius/inertia, all-weight Galois realization and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourceGammaOneDifferentialInputsProductionAudit8335.lean',p/'source-gamma-one-differential-inputs-8335-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production8335.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/gamma-one-arithmetic-geometry-20261026-626'
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
    "productionModules": 8335, "modules": newmods, "queries": queries,
    "theoremRegistrations": theorems, "constructionRegistrations": defs,
    "sourceHashes": {mapping[t.stem]: sha(t) for t, _ in pending}, "scratchCertificates": certs,
    "exactDependency": dependency, "assumptionsDischarged": discharged, "stillOpen": boundary,
    "status": status, "rootPinsChanged": False, "proofLimitsChanged": False,
    "promotionChanges": 'Only scratch imports are qualified. Every audited statement, proof body and comment is preserved. Original coefficient endomorphisms, literal q-expansion fields, genuine modular forms and both integral equations retain their definitions. No source contract is weakened.',
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
arch.write_text(arch.read_text(encoding='utf-8').replace(edge,'  GAMMAONEFIELDS8316["Actual Gamma1 fields, finite maps, Picard Hecke and arithmetic equivariance (DUB-17/18)"] --> GAMMAONEDIFF8335\n  GAMMAONEDIFF8335["Exact geometric H1 with original coefficient action; actual curve/scalar fields and both cusp differential integral equations proved. Regularity, full differential/Picard/H1/diamond comparison, original finite-character Galois realization and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'),encoding='utf-8')



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Actual Gamma1 cohomology and differential inputs - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-gamma-one-differential-inputs.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub(r'  logInfo m!".*"\n',
    '  logInfo m!"SOURCE GAMMA ONE DIFFERENTIAL INPUTS AUDIT PASS: {count} theorems including private/generated declarations. Exact geometric H1 retains the original coefficient action; actual curve/scalar fields and both differential integral equations are proved. Regularity, full differential/Picard/H1/diamond comparison, arithmetic realization and higher continuation remain required; 16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourceGammaOneDifferentialInputsProductionAudit8335.lean").write_text(out, encoding="utf-8")
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
    target = p / (source.stem + "Production8335.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
(p / "source-gamma-one-differential-inputs-8335-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 8335, "increment": 19, "queries": 85,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
