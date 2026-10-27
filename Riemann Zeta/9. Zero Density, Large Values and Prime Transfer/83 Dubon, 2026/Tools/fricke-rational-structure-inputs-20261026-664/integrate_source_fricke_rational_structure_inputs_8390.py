from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 8360
assert d["appliedSourceGammaOneRegularityFrickeInputs"]["receipt8360"]["exit"] == 0
assert (p / "paper-verification-8360-console.exit").read_text().strip() == "0"
assert (r/'Tools/gamma-one-regularity-fricke-inputs-20261026-653/canonical-evidence-8360.json').exists()
key = "appliedSourceFrickeRationalStructureInputs"
assert key not in d
digests = {'source-fricke-cyclotomic-transport-3-scratch-receipt.json': 'E44D705E88DA0B3DF3AFB519601CB8AF560A459EB90284E5A3FBA5EA51C56CC1', 'source-fricke-product-transport-4-scratch-receipt.json': '4AE13D58D0745E22B3D00FCB8FABFD41E76C0B72FF85C650159C2929D4F6EA94', 'source-fricke-separation-5-scratch-receipt.json': '176B0C3D74073586D550A442319F7527B30E77DFD3D50D302E1C918B9D01597D', 'source-level-one-analytic-polynomial-3-scratch-receipt.json': '49256FC40BD57DE11D337B120A8EB6DD987B4661D3509436CE3ACA27EFC52A1D', 'source-fricke-level-field-7d-scratch-receipt.json': 'DADA7AC2A4D909BEC106D53437F5F90A2054993FF1A234793972906F3649BDD2', 'source-fricke-stable-family-5c-scratch-receipt.json': 'B1DF4E3D301A85E7BA75EA3204A4239A254484895B7191DF1CF9E7530268A842', 'source-fricke-orbit-monic-2b-scratch-receipt.json': '46DF161D5C44AB8D5D94B89CDE615B6F63617F266587BF94D072B54CB80795A2', 'source-fricke-j-transcendence-1-scratch-receipt.json': '7D49A44AF9BFE468AEAECEB5D8A9EC7F51E8BD4AFB1415B59FF847C3D1C48821'}

for name, digest in digests.items():
    assert sha(p / name) == digest
certs = [json.loads((p / name).read_text(encoding="utf-8")) for name in digests]
mods = [m for z in certs for m in z["modules"]]
queries = [q for z in certs for q in z["queries"]]
theorems = [q for z in certs for q in z["theoremRegistrations"]]
defs = [q for z in certs for q in z["constructionRegistrations"]]
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (30, 30, 192, 140, 52)
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
archive_rel='Tools/fricke-rational-structure-inputs-20261026-664'
evidence=[p/'fricke-rational-structure-inputs-promotion-route-664.json']
evidence += [p/n for n in ['SourceFrickeCyclotomicTransportAudit3.exit', 'SourceFrickeCyclotomicTransportAudit3.lean', 'SourceFrickeCyclotomicTransportAudit3.log', 'SourceFrickeCyclotomicTransportDependencyAudit3.exit', 'SourceFrickeCyclotomicTransportDependencyAudit3.lean', 'SourceFrickeCyclotomicTransportDependencyAudit3.log', 'SourceFrickeFixedFieldJ.exit', 'SourceFrickeFixedFieldJ.lean', 'SourceFrickeFixedFieldJ.log', 'SourceFrickeFixedFieldJV2.exit', 'SourceFrickeFixedFieldJV2.lean', 'SourceFrickeFixedFieldJV2.log', 'SourceFrickeFixedFraction.exit', 'SourceFrickeFixedFraction.lean', 'SourceFrickeFixedFraction.log', 'SourceFrickeFixedFractionV2.exit', 'SourceFrickeFixedFractionV2.lean', 'SourceFrickeFixedFractionV2.log', 'SourceFrickeHolomorphicAlgebra.exit', 'SourceFrickeHolomorphicAlgebra.lean', 'SourceFrickeHolomorphicAlgebra.log', 'SourceFrickeHolomorphicAlgebraV2.exit', 'SourceFrickeHolomorphicAlgebraV2.lean', 'SourceFrickeHolomorphicAlgebraV2.log', 'SourceFrickeJTranscendenceAudit1.exit', 'SourceFrickeJTranscendenceAudit1.lean', 'SourceFrickeJTranscendenceAudit1.log', 'SourceFrickeJTranscendenceDependencyAudit1.exit', 'SourceFrickeJTranscendenceDependencyAudit1.lean', 'SourceFrickeJTranscendenceDependencyAudit1.log', 'SourceFrickeLevelAlgebra.exit', 'SourceFrickeLevelAlgebra.lean', 'SourceFrickeLevelAlgebra.log', 'SourceFrickeLevelAlgebraV2.exit', 'SourceFrickeLevelAlgebraV2.lean', 'SourceFrickeLevelAlgebraV2.log', 'SourceFrickeLevelField.exit', 'SourceFrickeLevelField.lean', 'SourceFrickeLevelField.log', 'SourceFrickeLevelFieldAudit7.exit', 'SourceFrickeLevelFieldAudit7.lean', 'SourceFrickeLevelFieldAudit7.log', 'SourceFrickeLevelFieldAudit7b.exit', 'SourceFrickeLevelFieldAudit7b.lean', 'SourceFrickeLevelFieldAudit7b.log', 'SourceFrickeLevelFieldAudit7c.exit', 'SourceFrickeLevelFieldAudit7c.lean', 'SourceFrickeLevelFieldAudit7c.log', 'SourceFrickeLevelFieldDependencyAudit7.lean', 'SourceFrickeLevelFieldDependencyAudit7b.lean', 'SourceFrickeLevelFieldDependencyAudit7c.exit', 'SourceFrickeLevelFieldDependencyAudit7c.lean', 'SourceFrickeLevelFieldDependencyAudit7c.log', 'SourceFrickeLevelFieldDependencyAudit7d.exit', 'SourceFrickeLevelFieldDependencyAudit7d.lean', 'SourceFrickeLevelFieldDependencyAudit7d.log', 'SourceFrickeLevelFieldV2.exit', 'SourceFrickeLevelFieldV2.lean', 'SourceFrickeLevelFieldV2.log', 'SourceFrickeLevelGroup.exit', 'SourceFrickeLevelGroup.lean', 'SourceFrickeLevelGroup.log', 'SourceFrickeLevelGroupV2.exit', 'SourceFrickeLevelGroupV2.lean', 'SourceFrickeLevelGroupV2.log', 'SourceFrickeModularOrbit.exit', 'SourceFrickeModularOrbit.lean', 'SourceFrickeModularOrbit.log', 'SourceFrickeOrbitMonicAudit2.exit', 'SourceFrickeOrbitMonicAudit2.lean', 'SourceFrickeOrbitMonicAudit2.log', 'SourceFrickeOrbitMonicAudit2b.exit', 'SourceFrickeOrbitMonicAudit2b.lean', 'SourceFrickeOrbitMonicAudit2b.log', 'SourceFrickeOrbitMonicDependencyAudit2.exit', 'SourceFrickeOrbitMonicDependencyAudit2.lean', 'SourceFrickeOrbitMonicDependencyAudit2.log', 'SourceFrickeOrbitMonicDependencyAudit2b.exit', 'SourceFrickeOrbitMonicDependencyAudit2b.lean', 'SourceFrickeOrbitMonicDependencyAudit2b.log', 'SourceFrickePoleBounded.exit', 'SourceFrickePoleBounded.lean', 'SourceFrickePoleBounded.log', 'SourceFrickePoleBoundedV2.exit', 'SourceFrickePoleBoundedV2.lean', 'SourceFrickePoleBoundedV2.log', 'SourceFrickeProductTransportAudit4.exit', 'SourceFrickeProductTransportAudit4.lean', 'SourceFrickeProductTransportAudit4.log', 'SourceFrickeProductTransportDependencyAudit4.exit', 'SourceFrickeProductTransportDependencyAudit4.lean', 'SourceFrickeProductTransportDependencyAudit4.log', 'SourceFrickeSeparationAudit5.exit', 'SourceFrickeSeparationAudit5.lean', 'SourceFrickeSeparationAudit5.log', 'SourceFrickeSeparationDependencyAudit5.exit', 'SourceFrickeSeparationDependencyAudit5.lean', 'SourceFrickeSeparationDependencyAudit5.log', 'SourceFrickeStableAlgebra.exit', 'SourceFrickeStableAlgebra.lean', 'SourceFrickeStableAlgebra.log', 'SourceFrickeStableEmbedding.exit', 'SourceFrickeStableEmbedding.lean', 'SourceFrickeStableEmbedding.log', 'SourceFrickeStableFamilyAudit5.exit', 'SourceFrickeStableFamilyAudit5.lean', 'SourceFrickeStableFamilyAudit5.log', 'SourceFrickeStableFamilyAudit5b.exit', 'SourceFrickeStableFamilyAudit5b.lean', 'SourceFrickeStableFamilyAudit5b.log', 'SourceFrickeStableFamilyDependencyAudit5.lean', 'SourceFrickeStableFamilyDependencyAudit5b.exit', 'SourceFrickeStableFamilyDependencyAudit5b.lean', 'SourceFrickeStableFamilyDependencyAudit5b.log', 'SourceFrickeStableFamilyDependencyAudit5c.exit', 'SourceFrickeStableFamilyDependencyAudit5c.lean', 'SourceFrickeStableFamilyDependencyAudit5c.log', 'SourceFrickeStableField.exit', 'SourceFrickeStableField.lean', 'SourceFrickeStableField.log', 'SourceFrickeStableFraction.exit', 'SourceFrickeStableFraction.lean', 'SourceFrickeStableFraction.log', 'SourceFrickeStableGroup.exit', 'SourceFrickeStableGroup.lean', 'SourceFrickeStableGroup.log', 'SourceFrickeStableMonic.exit', 'SourceFrickeStableMonic.lean', 'SourceFrickeStableMonic.log', 'SourceLevelOneAnalyticPolynomialAudit3.exit', 'SourceLevelOneAnalyticPolynomialAudit3.lean', 'SourceLevelOneAnalyticPolynomialAudit3.log', 'SourceLevelOneAnalyticPolynomialDependencyAudit3.exit', 'SourceLevelOneAnalyticPolynomialDependencyAudit3.lean', 'SourceLevelOneAnalyticPolynomialDependencyAudit3.log', 'consumers656.txt', 'fetch_fricke_base_change_dependencies_662.py', 'fetch_fricke_level_structure_656.py', 'fetch_fricke_rational_descent_661.py', 'fricke-base-change-dependencies-reuse-assessment-662.json', 'fricke-cyclotomic-transport-route-652.json', 'fricke-j-transcendence-local-reuse-route-663.json', 'fricke-level-field-route-658.json', 'fricke-level-field-route-658d.json', 'fricke-level-structure-reuse-assessment-656.json', 'fricke-orbit-monic-local-reuse-route-660.json', 'fricke-orbit-monic-local-reuse-route-660b.json', 'fricke-product-transport-route-654.json', 'fricke-rational-descent-reuse-assessment-661.json', 'fricke-separation-local-reuse-route-655.json', 'fricke-stable-family-route-659.json', 'fricke-stable-family-route-659b.json', 'fricke-stable-family-route-659c.json', 'level-one-analytic-polynomial-route-657.json', 'modules656.json', 'prepare_fricke_cyclotomic_transport_652.py', 'prepare_fricke_cyclotomic_transport_audit_652.py', 'prepare_fricke_j_transcendence_audit_663.py', 'prepare_fricke_level_dependency_658d.py', 'prepare_fricke_level_field_audit_658.py', 'prepare_fricke_level_field_audit_658b.py', 'prepare_fricke_level_field_audit_658c.py', 'prepare_fricke_level_field_v2_658b.py', 'prepare_fricke_orbit_monic_audit_660.py', 'prepare_fricke_orbit_monic_audit_660b.py', 'prepare_fricke_product_transport_audit_654.py', 'prepare_fricke_separation_audit_655.py', 'prepare_fricke_stable_documented_successor_659b.py', 'prepare_fricke_stable_family_659.py', 'prepare_fricke_stable_family_audit_659.py', 'prepare_fricke_stable_family_audit_659b.py', 'prepare_level_one_analytic_polynomial_audit_657.py', 'record656.py', 'record_fricke_cyclotomic_transport_652.py', 'record_fricke_j_transcendence_663.py', 'record_fricke_level_field_658d.py', 'record_fricke_orbit_monic_660b.py', 'record_fricke_product_transport_654.py', 'record_fricke_separation_655.py', 'record_fricke_stable_family_659c.py', 'record_level_one_analytic_polynomial_657.py', 'register656.py', 'registrations656.json', 'section656.txt', 'source-fricke-cyclotomic-transport-3-audit-config.json', 'source-fricke-cyclotomic-transport-3-scratch-receipt.json', 'source-fricke-j-transcendence-1-audit-config.json', 'source-fricke-j-transcendence-1-scratch-receipt.json', 'source-fricke-level-field-7d-audit-config.json', 'source-fricke-level-field-7d-scratch-receipt.json', 'source-fricke-orbit-monic-2b-audit-config.json', 'source-fricke-orbit-monic-2b-scratch-receipt.json', 'source-fricke-product-transport-4-audit-config.json', 'source-fricke-product-transport-4-scratch-receipt.json', 'source-fricke-separation-5-audit-config.json', 'source-fricke-separation-5-scratch-receipt.json', 'source-fricke-stable-family-5c-audit-config.json', 'source-fricke-stable-family-5c-scratch-receipt.json', 'source-level-one-analytic-polynomial-3-audit-config.json', 'source-level-one-analytic-polynomial-3-scratch-receipt.json', 'status656.txt']]
for folder in ['fricke-level-structure-reuse-656', 'fricke-rational-descent-reuse-661', 'fricke-base-change-dependencies-reuse-662', 'fricke-level-field-api-failure-658', 'fricke-level-field-instance-failure-658', 'fricke-fixed-field-j-instance-failure-658', 'fricke-fixed-field-j-action-failure-658', 'fricke-stable-field-instance-failure-659', 'fricke-stable-v2-before-variable-cleanup-659b']:
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
supplemental_review_path=r/archive_rel/'fricke-rational-structure-inputs-promotion-route-664.json'

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
reuse_path = r / "Tools/source-fricke-rational-structure-inputs.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt8360"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> arithmetic realization of original finite Gamma1 Hecke characters -> actual Picard/H1, full/parabolic and diamond comparison retaining the original homogeneous coefficient endomorphism -> actual regular differential/cusp comparison -> cyclotomic rational Fourier spanning -> Fricke fractions and integral relations.'
discharged = 'Actual torsion Fourier coefficients and the actual Fricke numerator transport under cyclotomic embeddings. The proved period map separates actual torsion Weierstrass values up to sign, giving the exact Fricke action kernel. The existing level-one Laurent polynomial identity transfers to actual analytic forms: weight 12m forms are Delta^m times a polynomial in actual j of degree at most m. The fixed subfield of the actual Fricke fraction field is exactly C(j), with degree the exact stabilizer index. A holomorphic principal-level invariant function with finite cusp poles at every modular translate is an actual Fricke fraction and satisfies an actual monic equation over C[j]; its modular orbit, the surjectivity of the fraction-field inclusion and the monic relation are derived. Existing actual j surjectivity proves its transcendence in the actual Fricke field. No fraction representation, fixed-field equality, monic relation, separation or transcendence premise is supplied.'
boundary = 'Cyclotomic integral base change, rational Fourier spanning and the actual algebraic realization of arbitrary Gamma1 cusp forms remain; the converse regular-differential-to-cusp construction also remains. The actual Picard/H1, full/parabolic, transpose and diamond comparison must identify the original finite homogeneous-coefficient Hecke characters with geometric characters. Frobenius/inertia, arithmetic realization of these characters, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain required. Neither complex semisimplicity, finite characters, Witt coefficients nor a universal deformation ring supplies a characteristic-zero lift or point. 16/20; DUB-17--20 OPEN.'
status = 'The actual Fricke rational-structure inputs pass 262 exhaustive scratch theorem checks and 192 public axiom queries across 30 modules, with sixteen linters per module and zero diagnostics. Eight declaration-value audits verify 224 required dependencies. Production aggregate, focused audit and sequential foundation/paper verification of the 8,390-module scope are pending.'
route = 'The renewed search is recorded in Dubon Reuse Search 2026-10-26.md. Fixed-revision primary snapshots and selected-file assessments are archived here. Reuse the actual elliptic period map for separation, the existing sparse Fourier reindexing and native Eisenstein coefficients for rational prefactors, the proved level-one Laurent polynomial identity for invariant analytic functions, native finite-action characteristic polynomials for the monic relation, and actual j surjectivity for transcendence. Native fixed-field degree and a finite orbit denominator prove stable-family fraction realization. Existing Laurent coefficient retraction and scalar independence are candidates for the next descent step; their Fourier-realization bridges remain unproved. The new external integral-span and constant-extension sources are research only, with no full external import-closure verification claim. Earlier source/object evidence affected by variable cleanup is not used for promotion; the final V3/V2 sources have fresh sequential builds and audits. Failed API, typeclass, linter and named-dependency evidence is retained. Native scalar aliases absent from terminal values retain explicit axiom checks without a named-use claim. No audited source or used audit is rewritten. No external project was built or imported; pins, proof limits and all twenty acceptance gates are unchanged.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Actual Fricke rational-structure inputs (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 8,360-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
corrections = []
count = sum(z['exhaustiveTheorems'] for z in certs)
assert count == 262

docpaths = list(dict.fromkeys(r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]))
for f in docpaths:
    assert "\n\n" in f.read_text(encoding="utf-8")
readmes = [(r.parent / "README.md", "Current Project 83 status ("), (repo / "README.md", "Project 83 has an ")]
for f, prefix in readmes:
    assert sum(line.startswith(prefix) for line in f.read_text(encoding="utf-8").splitlines()) == 1
arch = r / "Dubon Architecture.md"
edge = '  GAMMAONEREG8360["Actual Gamma1 cusp-matching differentials are regular; original Fricke transformation, holomorphy, torsion cyclotomic Fourier coefficients and cusp bounds proved. Rational spanning, realization, converse, Picard/H1/diamond, arithmetic realization and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourceFrickeRationalStructureInputsProductionAudit8390.lean',p/'source-fricke-rational-structure-inputs-8390-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production8390.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/gamma-one-regularity-fricke-inputs-20261026-653'
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
    "productionModules": 8390, "modules": newmods, "queries": queries,
    "theoremRegistrations": theorems, "constructionRegistrations": defs,
    "sourceHashes": {mapping[t.stem]: sha(t) for t, _ in pending}, "scratchCertificates": certs,
    "exactDependency": dependency, "assumptionsDischarged": discharged, "stillOpen": boundary,
    "status": status, "rootPinsChanged": False, "proofLimitsChanged": False,
    "promotionChanges": 'Only scratch imports are qualified. Every final audited statement, proof body and comment is preserved. All functions, torsion indices, coefficient fields, algebras, actions and embeddings are the actual constructed objects. No source contract is weakened.',
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
arch.write_text(arch.read_text(encoding='utf-8').replace(edge,'  GAMMAONEREG8360["Actual Gamma1 cusp-matching regularity and original Fricke Fourier inputs (DUB-17/18)"] --> FRICKERAT8390\n  FRICKERAT8390["Actual cyclotomic transport, Fricke separation, fixed field C(j), stable-family fraction realization and monic relations proved. Rational spanning, differential realization, converse, Picard/H1/diamond, original arithmetic realization and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'),encoding='utf-8')



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Actual Fricke rational-structure inputs - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-fricke-rational-structure-inputs.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub('  logInfo m!".*"\n', '  logInfo m!"SOURCE FRICKE RATIONAL STRUCTURE INPUTS AUDIT PASS: {count} theorems including private/generated declarations. Actual cyclotomic transport, Fricke separation, fixed field, stable-family fractions, monic relations and j transcendence are proved. Rational spanning, differential realization and arithmetic comparison remain; 16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourceFrickeRationalStructureInputsProductionAudit8390.lean").write_text(out, encoding="utf-8")
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
    target = p / (source.stem + "Production8390.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
(p / "source-fricke-rational-structure-inputs-8390-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 8390, "increment": 30, "queries": 192,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
