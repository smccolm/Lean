from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 8390
assert d["appliedSourceFrickeRationalStructureInputs"]["receipt8390"]["exit"] == 0
assert (p / "paper-verification-8390-console.exit").read_text().strip() == "0"
assert (r/'Tools/fricke-rational-structure-inputs-20261026-664/canonical-evidence-8390.json').exists()
key = "appliedSourceFrickeCyclotomicFourierSpan"
assert key not in d
digests = {'source-fricke-cyclotomic-descent-10-scratch-receipt.json': '2F13189E8EC3B130D64120AA5233F0C1B5BB5ED0F18F502FB34C707C3F0CB8C7', 'source-algebraic-constant-integral-span-5-scratch-receipt.json': '10B43BC49F115B9943B30B16E003BF9E49E899238C8D6B7056B67E4703843916', 'source-transcendental-constant-integral-span-7e-scratch-receipt.json': 'BEB97FB3DFD9C350FEEA1FB6CBDA75C922820B58AFAFB6BB1F1C6A94AD8484F0', 'source-laurent-integral-constant-span-6-scratch-receipt.json': 'A3985CA46443B6F18C4722CB81B0EA8B90DEA175ABE27A9684CCDFD4DC7E04EF', 'source-actual-fricke-laurent-integral-span-4-scratch-receipt.json': '1AA9BE753A398EA8006802834BD5FE08A0C5C4E71C01167E2833A04FAB9EF896', 'source-fricke-holomorphic-integral-span-8-scratch-receipt.json': '42312FD5920DB80060B5499758377769BD2FBCC10ECC479183FA00A789329C89', 'source-fricke-pole-cleared-fourier-span-2-scratch-receipt.json': '91444231DC17D0CEFFECD0187EFC8DC22B1A4C5780686625AD0C27A41F3CA29F'}

for name, digest in digests.items():
    assert sha(p / name) == digest
certs = [json.loads((p / name).read_text(encoding="utf-8")) for name in digests]
mods = [m for z in certs for m in z["modules"]]
queries = [q for z in certs for q in z["queries"]]
theorems = [q for z in certs for q in z["theoremRegistrations"]]
defs = [q for z in certs for q in z["constructionRegistrations"]]
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (42, 42, 154, 137, 17)
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
archive_rel='Tools/fricke-cyclotomic-fourier-span-20261026-673'
evidence=[p/'fricke-cyclotomic-fourier-span-promotion-route-673.json']
evidence += [p/n for n in ['LaurentIntegralSpanTypeProbe669.exit', 'LaurentIntegralSpanTypeProbe669.lean', 'LaurentIntegralSpanTypeProbe669.log', 'SourceActualFrickeLaurentIntegralSpanAudit4.exit', 'SourceActualFrickeLaurentIntegralSpanAudit4.lean', 'SourceActualFrickeLaurentIntegralSpanAudit4.log', 'SourceActualFrickeLaurentIntegralSpanDependencyAudit4.exit', 'SourceActualFrickeLaurentIntegralSpanDependencyAudit4.lean', 'SourceActualFrickeLaurentIntegralSpanDependencyAudit4.log', 'SourceAlgebraicConstantIntegralSpanAudit5.exit', 'SourceAlgebraicConstantIntegralSpanAudit5.lean', 'SourceAlgebraicConstantIntegralSpanAudit5.log', 'SourceAlgebraicConstantIntegralSpanDependencyAudit5.exit', 'SourceAlgebraicConstantIntegralSpanDependencyAudit5.lean', 'SourceAlgebraicConstantIntegralSpanDependencyAudit5.log', 'SourceFrickeCyclotomicDescentAudit10.exit', 'SourceFrickeCyclotomicDescentAudit10.lean', 'SourceFrickeCyclotomicDescentAudit10.log', 'SourceFrickeCyclotomicDescentDependencyAudit10.exit', 'SourceFrickeCyclotomicDescentDependencyAudit10.lean', 'SourceFrickeCyclotomicDescentDependencyAudit10.log', 'SourceFrickeHolomorphicIntegralSpanAudit8.exit', 'SourceFrickeHolomorphicIntegralSpanAudit8.lean', 'SourceFrickeHolomorphicIntegralSpanAudit8.log', 'SourceFrickeHolomorphicIntegralSpanDependencyAudit8.exit', 'SourceFrickeHolomorphicIntegralSpanDependencyAudit8.lean', 'SourceFrickeHolomorphicIntegralSpanDependencyAudit8.log', 'SourceFrickePoleClearedFourierSpanAudit2.exit', 'SourceFrickePoleClearedFourierSpanAudit2.lean', 'SourceFrickePoleClearedFourierSpanAudit2.log', 'SourceFrickePoleClearedFourierSpanDependencyAudit2.exit', 'SourceFrickePoleClearedFourierSpanDependencyAudit2.lean', 'SourceFrickePoleClearedFourierSpanDependencyAudit2.log', 'SourceLaurentIntegralConstantSpanAudit6.exit', 'SourceLaurentIntegralConstantSpanAudit6.lean', 'SourceLaurentIntegralConstantSpanAudit6.log', 'SourceLaurentIntegralConstantSpanDependencyAudit6.exit', 'SourceLaurentIntegralConstantSpanDependencyAudit6.lean', 'SourceLaurentIntegralConstantSpanDependencyAudit6.log', 'SourceTranscendentalConstantAlgebra.exit', 'SourceTranscendentalConstantAlgebra.lean', 'SourceTranscendentalConstantAlgebra.log', 'SourceTranscendentalConstantAlgebraV2.exit', 'SourceTranscendentalConstantAlgebraV2.lean', 'SourceTranscendentalConstantAlgebraV2.log', 'SourceTranscendentalConstantDenominators.exit', 'SourceTranscendentalConstantDenominators.lean', 'SourceTranscendentalConstantDenominators.log', 'SourceTranscendentalConstantDenominatorsV2.exit', 'SourceTranscendentalConstantDenominatorsV2.lean', 'SourceTranscendentalConstantDenominatorsV2.log', 'SourceTranscendentalConstantDiscovery667.exit', 'SourceTranscendentalConstantDiscovery667.lean', 'SourceTranscendentalConstantDiscovery667.log', 'SourceTranscendentalConstantEvaluation.exit', 'SourceTranscendentalConstantEvaluation.lean', 'SourceTranscendentalConstantEvaluation.log', 'SourceTranscendentalConstantEvaluationV2.exit', 'SourceTranscendentalConstantEvaluationV2.lean', 'SourceTranscendentalConstantEvaluationV2.log', 'SourceTranscendentalConstantFieldRange.exit', 'SourceTranscendentalConstantFieldRange.lean', 'SourceTranscendentalConstantFieldRange.log', 'SourceTranscendentalConstantFieldRangeV2.exit', 'SourceTranscendentalConstantFieldRangeV2.lean', 'SourceTranscendentalConstantFieldRangeV2.log', 'SourceTranscendentalConstantIntegralSpan.exit', 'SourceTranscendentalConstantIntegralSpan.lean', 'SourceTranscendentalConstantIntegralSpan.log', 'SourceTranscendentalConstantIntegralSpanAudit7.exit', 'SourceTranscendentalConstantIntegralSpanAudit7.lean', 'SourceTranscendentalConstantIntegralSpanAudit7.log', 'SourceTranscendentalConstantIntegralSpanAudit7e.exit', 'SourceTranscendentalConstantIntegralSpanAudit7e.lean', 'SourceTranscendentalConstantIntegralSpanAudit7e.log', 'SourceTranscendentalConstantIntegralSpanDependencyAudit7.lean', 'SourceTranscendentalConstantIntegralSpanDependencyAudit7e.exit', 'SourceTranscendentalConstantIntegralSpanDependencyAudit7e.lean', 'SourceTranscendentalConstantIntegralSpanDependencyAudit7e.log', 'SourceTranscendentalConstantIntegralSpanV2.exit', 'SourceTranscendentalConstantIntegralSpanV2.lean', 'SourceTranscendentalConstantIntegralSpanV2.log', 'SourceTranscendentalConstantNormality.exit', 'SourceTranscendentalConstantNormality.lean', 'SourceTranscendentalConstantNormality.log', 'SourceTranscendentalConstantNormalityV2.exit', 'SourceTranscendentalConstantNormalityV2.lean', 'SourceTranscendentalConstantNormalityV2.log', 'SourceTranscendentalConstantScaledRelation.exit', 'SourceTranscendentalConstantScaledRelation.lean', 'SourceTranscendentalConstantScaledRelation.log', 'SourceTranscendentalConstantScaledRelationV2.exit', 'SourceTranscendentalConstantScaledRelationV2.lean', 'SourceTranscendentalConstantScaledRelationV2.log', 'actual-fricke-laurent-integral-span-route-670.json', 'algebraic-constant-integral-span-route-666.json', 'consumers671.txt', 'fricke-cyclotomic-descent-local-reuse-route-665.json', 'fricke-holomorphic-integral-span-route-671.json', 'fricke-pole-cleared-fourier-span-route-672.json', 'laurent-integral-constant-span-route-669.json', 'modules671.json', 'prepare_actual_fricke_laurent_integral_span_audit_670.py', 'prepare_algebraic_constant_integral_span_666.py', 'prepare_algebraic_constant_integral_span_666b.py', 'prepare_algebraic_constant_integral_span_audit_666.py', 'prepare_fricke_cyclotomic_descent_audit_665.py', 'prepare_fricke_holomorphic_integral_span_audit_671.py', 'prepare_fricke_pole_cleared_fourier_span_audit_672.py', 'prepare_laurent_integral_constant_span_audit_669.py', 'prepare_transcendental_constant_integral_span_667.py', 'prepare_transcendental_constant_integral_span_audit_667d.py', 'prepare_transcendental_constant_integral_span_audit_667e.py', 'prepare_transcendental_constant_linter_successor_667e.py', 'record671.py', 'record_actual_fricke_laurent_integral_span_670.py', 'record_algebraic_constant_integral_span_666.py', 'record_fricke_cyclotomic_descent_665.py', 'record_fricke_cyclotomic_descent_665b.py', 'record_fricke_holomorphic_integral_span_671.py', 'record_fricke_holomorphic_integral_span_671b.py', 'record_fricke_pole_cleared_fourier_span_672.py', 'record_laurent_integral_constant_span_669.py', 'record_transcendental_constant_integral_span_667e.py', 'register671.py', 'registrations671.json', 'section671.txt', 'source-actual-fricke-laurent-integral-span-4-audit-config.json', 'source-actual-fricke-laurent-integral-span-4-scratch-receipt.json', 'source-algebraic-constant-integral-span-5-audit-config.json', 'source-algebraic-constant-integral-span-5-scratch-receipt.json', 'source-fricke-cyclotomic-descent-10-audit-config.json', 'source-fricke-cyclotomic-descent-10-scratch-receipt.json', 'source-fricke-holomorphic-integral-span-8-audit-config.json', 'source-fricke-holomorphic-integral-span-8-scratch-receipt.json', 'source-fricke-pole-cleared-fourier-span-2-audit-config.json', 'source-fricke-pole-cleared-fourier-span-2-scratch-receipt.json', 'source-laurent-integral-constant-span-6-audit-config.json', 'source-laurent-integral-constant-span-6-scratch-receipt.json', 'source-transcendental-constant-integral-span-7e-audit-config.json', 'source-transcendental-constant-integral-span-7e-scratch-receipt.json', 'status671.txt', 'transcendental-constant-discovery-667-config.json', 'transcendental-constant-integral-span-route-667.json', 'transcendental-constant-integral-span-route-667d.json', 'transcendental-constant-integral-span-route-667e.json']]
for folder in ['transcendental-constant-integral-span-failed-667a', 'transcendental-constant-field-range-failed-667b', 'transcendental-constant-pretrim-667c']:
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
supplemental_review_path=r/archive_rel/'fricke-cyclotomic-fourier-span-promotion-route-673.json'

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
reuse_path = r / "Tools/source-fricke-cyclotomic-fourier-span.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt8390"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> arithmetic realization of original finite Gamma1 Hecke characters -> actual Picard/H1, full/parabolic, transpose and diamond comparison retaining the original homogeneous coefficient endomorphism -> actual differential/cusp comparison -> rational cusp-form spanning -> pole-cleared cyclotomic Fourier span of actual Fricke functions.'
discharged = 'The original cyclotomic j/Fricke functions and their fractions have literal Laurent cusp representations. Coefficient retraction descends monic equations to the original field. Algebraic and transcendental simple-constant extensions, finite constant capture and coefficient-derived relative transcendence prove the integral Laurent span over the original constants. The actual finite Fricke generator family satisfies every finiteness, integrality, coefficient-field and transcendence premise. Integral Laurent summands lift to actual cyclotomic fractions; their cleared monic equations and the existing removable-singularity theorem derive holomorphic representatives. Native coefficientwise complex scalar multiplication and analytic uniqueness lift the Laurent span to actual functions. Positive discriminant cusp order clears each summand pole, and uniqueness against the cyclotomic Laurent expansion proves every resulting Fourier coefficient lies in the original cyclotomic field. Hence a holomorphic principal-level invariant function with the required bounds at every modular translate lies in the complex span of actual holomorphic functions with pole-cleared cyclotomic Fourier coefficients.'
boundary = 'Rational cusp-form spanning still requires the modular-weight, cusp-condition and coefficient-descent steps. The pole-cleared weight-zero function span does not yet realize an arbitrary Gamma1 cusp form as an original algebraic differential; the converse regular-differential-to-cusp construction also remains. The actual Picard/H1, full/parabolic, transpose and diamond comparison must identify original finite homogeneous-coefficient Hecke characters with geometric characters. Frobenius/inertia, arithmetic realization of those characters, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain. Complex semisimplicity, finite characters, Witt coefficients and universal deformation rings do not supply a characteristic-zero lift or point. 16/20; DUB-17--20 OPEN.'
status = 'The cyclotomic Fourier span passes 189 exhaustive scratch theorem checks and 154 public axiom queries across 42 modules, with sixteen linters per module and zero diagnostics. Seven declaration-value audits verify 225 required dependencies. Production aggregate, focused audit and sequential foundation/paper verification of the 8,432-module scope are pending.'
route = 'The renewed selected-file search is recorded in Dubon Reuse Search 2026-10-26.md. Adapt the fixed-revision primary simple-constant integral-span proofs to the actual Laurent field, deriving the relative transcendence premise from coefficients. Reuse native fraction-ring surjectivity, the existing expanded-j transcendence, finite-action monic relation, analytic cusp-germ injectivity, coefficient retraction, monic-root bound and removable-singularity extension. For Fourier coefficients, native meromorphic orders clear the cusp pole and existing Laurent representations identify coefficients directly; the external general valuation engine, analytic quotient file, recursive Fourier division and monic-growth development are unnecessary on this route. All used and failed audits, original failed source variants and fresh successors are retained. Only final audited sources are promoted and only imports are qualified. No external full import closure was built or certified; pins, proof limits, source contract and all twenty acceptance gates are unchanged.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Actual Fricke cyclotomic Fourier span (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 8,390-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
corrections = []
count = sum(z['exhaustiveTheorems'] for z in certs)
assert count == 189

docpaths = list(dict.fromkeys(r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]))
for f in docpaths:
    assert "\n\n" in f.read_text(encoding="utf-8")
readmes = [(r.parent / "README.md", "Current Project 83 status ("), (repo / "README.md", "Project 83 has an ")]
for f, prefix in readmes:
    assert sum(line.startswith(prefix) for line in f.read_text(encoding="utf-8").splitlines()) == 1
arch = r / "Dubon Architecture.md"
edge = '  FRICKERAT8390["Actual cyclotomic transport, Fricke separation, fixed field C(j), stable-family fraction realization and monic relations proved. Rational spanning, differential realization, converse, Picard/H1/diamond, original arithmetic realization and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourceFrickeCyclotomicFourierSpanProductionAudit8432.lean',p/'source-fricke-cyclotomic-fourier-span-8432-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production8432.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/fricke-rational-structure-inputs-20261026-664'
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
    "productionModules": 8432, "modules": newmods, "queries": queries,
    "theoremRegistrations": theorems, "constructionRegistrations": defs,
    "sourceHashes": {mapping[t.stem]: sha(t) for t, _ in pending}, "scratchCertificates": certs,
    "exactDependency": dependency, "assumptionsDischarged": discharged, "stillOpen": boundary,
    "status": status, "rootPinsChanged": False, "proofLimitsChanged": False,
    "promotionChanges": 'Only scratch imports are qualified. Every final audited statement, proof body and comment is preserved. Original cyclotomic fields, Laurent series, actual Fricke functions, modular orbits and the ordinary coefficientwise complex scalar action remain explicit. No source contract is weakened.',
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
arch.write_text(arch.read_text(encoding='utf-8').replace(edge,'  FRICKERAT8390["Actual Fricke fixed field, stable-family fractions and monic relations (DUB-17/18)"] --> FRICKEFOURIER8432\n  FRICKEFOURIER8432["Original-constant Laurent integral descent, holomorphic summand realization and pole-cleared cyclotomic Fourier span proved. Rational cusp spanning, differential realization, converse, Picard/H1/diamond, original arithmetic association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'),encoding='utf-8')



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Actual Fricke cyclotomic Fourier span - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-fricke-cyclotomic-fourier-span.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub('  logInfo m!".*"\n', '  logInfo m!"SOURCE FRICKE CYCLOTOMIC FOURIER SPAN AUDIT PASS: {count} theorems including private/generated declarations. Original-constant integral Laurent descent, holomorphic summand realization and pole-cleared cyclotomic Fourier span are proved. Rational cusp spanning, differential realization and arithmetic comparison remain; 16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourceFrickeCyclotomicFourierSpanProductionAudit8432.lean").write_text(out, encoding="utf-8")
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
    target = p / (source.stem + "Production8432.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
(p / "source-fricke-cyclotomic-fourier-span-8432-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 8432, "increment": 42, "queries": 154,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
