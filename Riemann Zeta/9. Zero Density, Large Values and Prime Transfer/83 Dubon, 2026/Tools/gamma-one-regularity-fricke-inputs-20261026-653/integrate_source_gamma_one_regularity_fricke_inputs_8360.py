from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 8335
assert d["appliedSourceGammaOneDifferentialInputs"]["receipt8335"]["exit"] == 0
assert (p / "paper-verification-8335-console.exit").read_text().strip() == "0"
assert (r/'Tools/gamma-one-differential-inputs-20261026-641/canonical-evidence-8335.json').exists()
key = "appliedSourceGammaOneRegularityFrickeInputs"
assert key not in d
digests = {'source-gamma-one-differential-regularity-6b-scratch-receipt.json': '9EF4347C9A2DF281E237481B678ECB69B39AFE7E5695EED82DB70603DCB9BEA7', 'source-fricke-transformation-4c-scratch-receipt.json': '1B089A904F7ECB171E895466FDC455922A1C2D8EBD06E3BD79EB6FC0E75C126E', 'source-weierstrass-expansion-8b-scratch-receipt.json': '8D69957DFF05891851A445E70D258A1014E88FC8F9D78733A17ED2BEF4FEC3AD', 'source-fricke-fourier-coefficients-7b-scratch-receipt.json': '29B8C452DEC9110ED125AECC5DF5407322B657D179909021828AA33681AA38E5'}

for name, digest in digests.items():
    assert sha(p / name) == digest
certs = [json.loads((p / name).read_text(encoding="utf-8")) for name in digests]
mods = [m for z in certs for m in z["modules"]]
queries = [q for z in certs for q in z["queries"]]
theorems = [q for z in certs for q in z["theoremRegistrations"]]
defs = [q for z in certs for q in z["constructionRegistrations"]]
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (25, 25, 152, 126, 26)
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
archive_rel='Tools/gamma-one-regularity-fricke-inputs-20261026-653'
evidence=[p/'gamma-one-regularity-fricke-inputs-promotion-route-653.json']
evidence += [p/n for n in ['SourceFrickeFourierCoefficientsAudit7.exit', 'SourceFrickeFourierCoefficientsAudit7.log', 'SourceFrickeFourierCoefficientsAudit7b.exit', 'SourceFrickeFourierCoefficientsAudit7b.lean', 'SourceFrickeFourierCoefficientsAudit7b.log', 'SourceFrickeFourierCoefficientsDependencyAudit7b.exit', 'SourceFrickeFourierCoefficientsDependencyAudit7b.lean', 'SourceFrickeFourierCoefficientsDependencyAudit7b.log', 'SourceFrickeFunctionTransformation.exit', 'SourceFrickeFunctionTransformation.lean', 'SourceFrickeFunctionTransformation.log', 'SourceFrickeModularLattice.exit', 'SourceFrickeModularLattice.lean', 'SourceFrickeModularLattice.log', 'SourceFrickePeriodHomothety.exit', 'SourceFrickePeriodHomothety.lean', 'SourceFrickePeriodHomothety.log', 'SourceFrickeTorsionTransformation.exit', 'SourceFrickeTorsionTransformation.lean', 'SourceFrickeTorsionTransformation.log', 'SourceFrickeTransformationAudit4.exit', 'SourceFrickeTransformationAudit4.lean', 'SourceFrickeTransformationAudit4.log', 'SourceFrickeTransformationAudit4b.exit', 'SourceFrickeTransformationAudit4b.lean', 'SourceFrickeTransformationAudit4b.log', 'SourceFrickeTransformationDependencyAudit4b.exit', 'SourceFrickeTransformationDependencyAudit4b.lean', 'SourceFrickeTransformationDependencyAudit4b.log', 'SourceFrickeTransformationDependencyAudit4c.exit', 'SourceFrickeTransformationDependencyAudit4c.lean', 'SourceFrickeTransformationDependencyAudit4c.log', 'SourceGammaOneDifferentialRegularityAudit6.exit', 'SourceGammaOneDifferentialRegularityAudit6.lean', 'SourceGammaOneDifferentialRegularityAudit6.log', 'SourceGammaOneDifferentialRegularityDependencyAudit6.exit', 'SourceGammaOneDifferentialRegularityDependencyAudit6.lean', 'SourceGammaOneDifferentialRegularityDependencyAudit6.log', 'SourceGammaOneDifferentialRegularityDependencyAudit6b.exit', 'SourceGammaOneDifferentialRegularityDependencyAudit6b.lean', 'SourceGammaOneDifferentialRegularityDependencyAudit6b.log', 'SourceWeierstrassExpansionAudit8.exit', 'SourceWeierstrassExpansionAudit8.lean', 'SourceWeierstrassExpansionAudit8.log', 'SourceWeierstrassExpansionDependencyAudit8.exit', 'SourceWeierstrassExpansionDependencyAudit8.lean', 'SourceWeierstrassExpansionDependencyAudit8.log', 'SourceWeierstrassExpansionDependencyAudit8b.exit', 'SourceWeierstrassExpansionDependencyAudit8b.lean', 'SourceWeierstrassExpansionDependencyAudit8b.log', 'consumers648.txt', 'fetch_fricke_torsion_expansion_648.py', 'fetch_gamma1_cusp_realization_644.py', 'fetch_gamma1_rational_structure_inputs_646.py', 'fetch_gamma1_regularity_descent_642.py', 'fetch_weierstrass_expansion_649.py', 'fricke-fourier-coefficients-route-651.json', 'fricke-fourier-coefficients-route-651b.json', 'fricke-torsion-expansion-reuse-assessment-648.json', 'fricke-transformation-documented-successor-647b.json', 'fricke-transformation-route-647.json', 'fricke-transformation-route-647c.json', 'gamma1-cusp-realization-reuse-assessment-644.json', 'gamma1-differential-regularity-route-643.json', 'gamma1-differential-regularity-route-643b.json', 'gamma1-rational-structure-input-reuse-assessment-646.json', 'gamma1-regularity-descent-reuse-assessment-642.json', 'modules648.json', 'prepare_fricke_dependency_successor_647c.py', 'prepare_fricke_documented_successor_647b.py', 'prepare_fricke_fourier_coefficients_651.py', 'prepare_fricke_fourier_coefficients_audit_651.py', 'prepare_fricke_fourier_coefficients_audit_651b.py', 'prepare_fricke_fourier_coefficients_record_651b.py', 'prepare_fricke_transformation_audit_647.py', 'prepare_fricke_transformation_audit_647b.py', 'prepare_fricke_transformation_record_647c.py', 'prepare_gamma_one_differential_regularity_audit_643.py', 'prepare_gamma_one_differential_regularity_scope_643.py', 'prepare_gamma_one_differential_regularity_successor_643b.py', 'prepare_weierstrass_expansion_650.py', 'prepare_weierstrass_expansion_audit_650.py', 'prepare_weierstrass_expansion_record_650b.py', 'record648.py', 'record_fricke_fourier_coefficients_651b.py', 'record_fricke_transformation_647c.py', 'record_gamma_one_differential_regularity_643.py', 'record_gamma_one_differential_regularity_643b.py', 'record_weierstrass_expansion_650b.py', 'register648.py', 'registrations648.json', 'section648.txt', 'source-fricke-fourier-coefficients-7b-audit-config.json', 'source-fricke-fourier-coefficients-7b-scratch-receipt.json', 'source-fricke-transformation-4c-audit-config.json', 'source-fricke-transformation-4c-scratch-receipt.json', 'source-gamma-one-differential-regularity-6b-audit-config.json', 'source-gamma-one-differential-regularity-6b-scratch-receipt.json', 'source-weierstrass-expansion-8b-audit-config.json', 'source-weierstrass-expansion-8b-scratch-receipt.json', 'status648.txt', 'weierstrass-expansion-reuse-assessment-649.json', 'weierstrass-expansion-route-650.json', 'weierstrass-expansion-route-650b.json']]
for folder in ['gamma1-regularity-descent-reuse-642', 'gamma1-cusp-realization-reuse-644', 'gamma1-rational-structure-input-reuse-646', 'fricke-torsion-expansion-reuse-648', 'weierstrass-expansion-reuse-649', 'gamma1-integral-descent-643-before-explicit-coefficient-transport', 'gamma1-regularity-643-before-order-name-repair', 'gamma1-regularity-643-before-field-independent-order-consumer']:
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
supplemental_review_path=r/archive_rel/'gamma-one-regularity-fricke-inputs-promotion-route-653.json'

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
reuse_path = r / "Tools/source-gamma-one-regularity-fricke-inputs.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt8335"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> arithmetic realization of original finite Gamma1 Hecke characters -> actual Picard/H1, full/parabolic and diamond comparison retaining the original homogeneous coefficient endomorphism -> actual regular differential/cusp comparison -> regularity and rational Fourier structure.'
discharged = 'For the actual Gamma1 integral-ratio Laurent field, every differential whose mapped expansion equals an actual weight-two cusp expansion is regular at every place. Both integral equations, coefficient descent, local orders and curve prerequisites are derived. The original normalized Fricke functions transform by the actual torsion-index action, are invariant under the principal subgroup and unchanged by index negation. Native Lipschitz summation and absolute Weierstrass summability prove the exact torsion Fourier formula and holomorphy. The actual normalized torsion functions are periodic, bounded at infinity and have explicit Fourier coefficients in the level cyclotomic field. Multiplication of the original Fricke function by Delta gives a bounded function at infinity. No regularity, Fourier identity, holomorphy, coefficient-field or cusp-bound premise is assumed.'
boundary = 'Algebraic realization of arbitrary Gamma1 cusp forms and the converse regular-differential-to-cusp construction remain. The actual Picard/H1, full/parabolic, transpose and diamond comparison must identify the original finite homogeneous-coefficient Hecke characters with geometric characters. Frobenius/inertia, arithmetic realization of these characters, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain required. Neither complex semisimplicity, finite characters, Witt coefficients nor a universal deformation ring supplies a characteristic-zero lift or point. 16/20; DUB-17--20 OPEN.'
status = 'The actual Gamma1 regularity and Fricke Fourier inputs pass 264 exhaustive scratch checks and 152 public axiom queries across 25 modules, with sixteen linters per module and zero diagnostics. Four declaration-value audits verify 162 required dependencies. Production aggregate, focused audit and sequential foundation/paper verification of the 8,360-module scope are pending.'
route = 'The renewed search is recorded in Dubon Reuse Search 2026-10-26.md; the exact fixed-revision primary proofs and adaptation assessments are archived here. Reuse a native linear retraction for coefficient descent, the previously proved actual Gamma1 integral equations and curve prerequisites, the actual Weierstrass lattice and native modular transformations. Native weight-two Lipschitz summation, absolute lattice summability, locally uniform differentiation and finite-product summability avoid duplicate foundations. Keep the integer-complement boundary case required by torsion points with first coordinate zero. Finite exponent fibers and native Fourier uniqueness give the actual cyclotomic coefficients. The rational Hecke-matrix basis does not supply the missing Gamma1 rational Fourier basis. Failed timeout, documentation, preflight and dependency-audit evidence is preserved with fresh successors. No used audit or audited mathematical body is rewritten. No external project was built or imported; pins, proof limits and all twenty gates are unchanged.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Actual Gamma1 regularity and Fricke Fourier inputs (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 8,335-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
corrections = []
count = sum(z['exhaustiveTheorems'] for z in certs)
assert count == 264

docpaths = list(dict.fromkeys(r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]))
for f in docpaths:
    assert "\n\n" in f.read_text(encoding="utf-8")
readmes = [(r.parent / "README.md", "Current Project 83 status ("), (repo / "README.md", "Project 83 has an ")]
for f, prefix in readmes:
    assert sum(line.startswith(prefix) for line in f.read_text(encoding="utf-8").splitlines()) == 1
arch = r / "Dubon Architecture.md"
edge = '  GAMMAONEDIFF8335["Exact geometric H1 with original coefficient action; actual curve/scalar fields and both cusp differential integral equations proved. Regularity, full differential/Picard/H1/diamond comparison, original finite-character Galois realization and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourceGammaOneRegularityFrickeInputsProductionAudit8360.lean',p/'source-gamma-one-regularity-fricke-inputs-8360-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production8360.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/gamma-one-differential-inputs-20261026-641'
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
    "productionModules": 8360, "modules": newmods, "queries": queries,
    "theoremRegistrations": theorems, "constructionRegistrations": defs,
    "sourceHashes": {mapping[t.stem]: sha(t) for t, _ in pending}, "scratchCertificates": certs,
    "exactDependency": dependency, "assumptionsDischarged": discharged, "stillOpen": boundary,
    "status": status, "rootPinsChanged": False, "proofLimitsChanged": False,
    "promotionChanges": 'Only scratch imports are qualified. Every audited statement, proof body and comment is preserved. Actual Gamma1 fields and native cusp forms retain their definitions; no regularity or integral equation is assumed. No source contract is weakened.',
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
arch.write_text(arch.read_text(encoding='utf-8').replace(edge,'  GAMMAONEDIFF8335["Exact geometric H1, actual fields and both integral equations (DUB-17/18)"] --> GAMMAONEREG8360\n  GAMMAONEREG8360["Actual Gamma1 cusp-matching differentials are regular; original Fricke transformation, holomorphy, torsion cyclotomic Fourier coefficients and cusp bounds proved. Rational spanning, realization, converse, Picard/H1/diamond, arithmetic realization and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'),encoding='utf-8')



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Actual Gamma1 regularity and Fricke Fourier inputs - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-gamma-one-regularity-fricke-inputs.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub('  logInfo m!".*"\n', '  logInfo m!"SOURCE GAMMA ONE REGULARITY FRICKE INPUTS AUDIT PASS: {count} theorems including private/generated declarations. Actual Gamma1 cusp-matching differentials are regular; original Fricke transformations, holomorphy and cyclotomic Fourier coefficients are proved. Rational spanning, realization, converse and arithmetic comparison remain; 16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourceGammaOneRegularityFrickeInputsProductionAudit8360.lean").write_text(out, encoding="utf-8")
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
    target = p / (source.stem + "Production8360.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
(p / "source-gamma-one-regularity-fricke-inputs-8360-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 8360, "increment": 25, "queries": 152,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
