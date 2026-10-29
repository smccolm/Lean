from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 9123
assert d["appliedSourceGammaOneTateFrobenius"]["receipt9123"]["exit"] == 0
assert (p / "paper-verification-9123-console.exit").read_text().strip() == "0"
assert (r/'Tools/gamma-one-tate-frobenius-20261028-1402/canonical-evidence-9123.json').exists()
key = "appliedSourceGammaOneGlobalGalois"
assert key not in d
digests = {'source-gamma-one-twisted-1-scratch-receipt.json': '3ECACA183103DEDE06FBEF5AA00D20AB00F1BA7D92D39027B3C38A9052DD0E77', 'source-gamma-one-continuity-1-scratch-receipt.json': 'A12486EA185DC51821A193A3570A78F8E5D2A0DA5485AD99DB8236CB71AD7AB8', 'source-gamma-one-arithmetic-orbit-2-scratch-receipt.json': '99649640136065EA0642922E7EE603631C8FEA8EB9DDD024115C4B4A740AB221'}

for name, digest in digests.items():
    assert sha(p / name) == digest
certs = [json.loads((p / name).read_text(encoding="utf-8")) for name in digests]
mods = [m for z in certs for m in z["modules"]]
queries = [q for z in certs for q in z["queries"]]
theorems = [q for z in certs for q in z["theoremRegistrations"]]
defs = [q for z in certs for q in z["constructionRegistrations"]]
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (26, 26, 39, 33, 6)
omitted = []
assert not set(mods).intersection(c["productionModules"])
mapping = {m: "Dubon2026." + m for m in c["productionModules"] + mods}
mapping["SourceGammaOneFiniteDivisorReciprocityAssembled"] = "Dubon2026.SourceGammaOneFiniteDivisorReciprocity"
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
        assert Path(item["compileExit"]).read_text().strip() == "0" and Path(item["compileLog"]).stat().st_size == 0
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
archive_rel='Tools/gamma-one-global-galois-20261028-1431'
evidence=[p/'gamma-one-global-galois-promotion-route-1431.json']
evidence += [p/n for n in ['Preflight1401.lean', 'Preflight1405.lean', 'Preflight1409.lean', 'Preflight1413.lean', 'Preflight1417.lean', 'Preflight1421.lean', 'Preflight1425.lean', 'Preflight1429.lean', 'SourceAbsoluteCyclotomicCharacter-1411.exit', 'SourceAbsoluteCyclotomicCharacter-1411.log', 'SourceAbsoluteCyclotomicCharacter.lean', 'SourceAbsoluteCyclotomicCharacter1400a.exit', 'SourceAbsoluteCyclotomicCharacter1400a.lean.txt', 'SourceAbsoluteCyclotomicCharacter1400a.log', 'SourceAbsoluteCyclotomicCharacter1400b.exit', 'SourceAbsoluteCyclotomicCharacter1400b.lean', 'SourceAbsoluteCyclotomicCharacter1400b.log', 'SourceAbsoluteCyclotomicLocal-1411.exit', 'SourceAbsoluteCyclotomicLocal-1411.log', 'SourceAbsoluteCyclotomicLocal.lean', 'SourceAbsoluteCyclotomicLocal1405a.exit', 'SourceAbsoluteCyclotomicLocal1405a.lean', 'SourceAbsoluteCyclotomicLocal1405a.log', 'SourceCyclotomicHomogeneousAction-1411.exit', 'SourceCyclotomicHomogeneousAction-1411.log', 'SourceCyclotomicHomogeneousAction.lean', 'SourceCyclotomicHomogeneousAction1399a.exit', 'SourceCyclotomicHomogeneousAction1399a.lean.txt', 'SourceCyclotomicHomogeneousAction1399a.log', 'SourceCyclotomicHomogeneousAction1399b.exit', 'SourceCyclotomicHomogeneousAction1399b.lean', 'SourceCyclotomicHomogeneousAction1399b.log', 'SourceCyclotomicHomogeneousDiamond-1429.exit', 'SourceCyclotomicHomogeneousDiamond-1429.log', 'SourceCyclotomicHomogeneousDiamond.lean', 'SourceCyclotomicHomogeneousDiamond1426a.exit', 'SourceCyclotomicHomogeneousDiamond1426a.lean', 'SourceCyclotomicHomogeneousDiamond1426a.log', 'SourceCyclotomicHomogeneousHecke-1411.exit', 'SourceCyclotomicHomogeneousHecke-1411.log', 'SourceCyclotomicHomogeneousHecke.lean', 'SourceCyclotomicHomogeneousHecke1403a.exit', 'SourceCyclotomicHomogeneousHecke1403a.lean.txt', 'SourceCyclotomicHomogeneousHecke1403a.log', 'SourceCyclotomicHomogeneousHecke1403b.exit', 'SourceCyclotomicHomogeneousHecke1403b.lean', 'SourceCyclotomicHomogeneousHecke1403b.log', 'SourceGammaOneArithmeticOrbitAudit1.exit', 'SourceGammaOneArithmeticOrbitAudit1.lean', 'SourceGammaOneArithmeticOrbitAudit1.log', 'SourceGammaOneArithmeticOrbitDependencyAudit1.exit', 'SourceGammaOneArithmeticOrbitDependencyAudit1.lean', 'SourceGammaOneArithmeticOrbitDependencyAudit1.log', 'SourceGammaOneArithmeticOrbitDependencyAudit2.exit', 'SourceGammaOneArithmeticOrbitDependencyAudit2.lean', 'SourceGammaOneArithmeticOrbitDependencyAudit2.log', 'SourceGammaOneArithmeticOrbitScratchOwnership1430.exit', 'SourceGammaOneArithmeticOrbitScratchOwnership1430.lean', 'SourceGammaOneArithmeticOrbitScratchOwnership1430.log', 'SourceGammaOneContinuityAudit1.exit', 'SourceGammaOneContinuityAudit1.lean', 'SourceGammaOneContinuityAudit1.log', 'SourceGammaOneContinuityDependencyAudit1.exit', 'SourceGammaOneContinuityDependencyAudit1.lean', 'SourceGammaOneContinuityDependencyAudit1.log', 'SourceGammaOneContinuityScratchOwnership1423.exit', 'SourceGammaOneContinuityScratchOwnership1423.lean', 'SourceGammaOneContinuityScratchOwnership1423.log', 'SourceGammaOneFinitePlaceOrbit-1422.exit', 'SourceGammaOneFinitePlaceOrbit-1422.log', 'SourceGammaOneFinitePlaceOrbit.lean', 'SourceGammaOneFinitePlaceOrbit1414a.exit', 'SourceGammaOneFinitePlaceOrbit1414a.lean.txt', 'SourceGammaOneFinitePlaceOrbit1414a.log', 'SourceGammaOneFinitePlaceOrbit1414b.exit', 'SourceGammaOneFinitePlaceOrbit1414b.lean', 'SourceGammaOneFinitePlaceOrbit1414b.log', 'SourceGammaOneFiniteTateDual-1422.exit', 'SourceGammaOneFiniteTateDual-1422.log', 'SourceGammaOneFiniteTateDual.lean', 'SourceGammaOneFiniteTateDual1418a.exit', 'SourceGammaOneFiniteTateDual1418a.lean.txt', 'SourceGammaOneFiniteTateDual1418a.log', 'SourceGammaOneFiniteTateDual1418b.exit', 'SourceGammaOneFiniteTateDual1418b.lean.txt', 'SourceGammaOneFiniteTateDual1418b.log', 'SourceGammaOneFiniteTateDual1418c.exit', 'SourceGammaOneFiniteTateDual1418c.lean', 'SourceGammaOneFiniteTateDual1418c.log', 'SourceGammaOneFunctionFieldDefinition-1422.exit', 'SourceGammaOneFunctionFieldDefinition-1422.log', 'SourceGammaOneFunctionFieldDefinition.lean', 'SourceGammaOneFunctionFieldDefinition1413a.exit', 'SourceGammaOneFunctionFieldDefinition1413a.lean', 'SourceGammaOneFunctionFieldDefinition1413a.log', 'SourceGammaOneParabolicGaloisFrobenius-1411.exit', 'SourceGammaOneParabolicGaloisFrobenius-1411.log', 'SourceGammaOneParabolicGaloisFrobenius.lean', 'SourceGammaOneParabolicGaloisFrobenius1410a.exit', 'SourceGammaOneParabolicGaloisFrobenius1410a.lean.txt', 'SourceGammaOneParabolicGaloisFrobenius1410a.log', 'SourceGammaOneParabolicGaloisFrobenius1410b.exit', 'SourceGammaOneParabolicGaloisFrobenius1410b.lean', 'SourceGammaOneParabolicGaloisFrobenius1410b.log', 'SourceGammaOneParabolicGaloisOrbit-1429.exit', 'SourceGammaOneParabolicGaloisOrbit-1429.log', 'SourceGammaOneParabolicGaloisOrbit.lean', 'SourceGammaOneParabolicGaloisOrbit1428a.exit', 'SourceGammaOneParabolicGaloisOrbit1428a.lean', 'SourceGammaOneParabolicGaloisOrbit1428a.log', 'SourceGammaOneParabolicTateLift-1411.exit', 'SourceGammaOneParabolicTateLift-1411.log', 'SourceGammaOneParabolicTateLift.lean', 'SourceGammaOneParabolicTateLift1409a.exit', 'SourceGammaOneParabolicTateLift1409a.lean', 'SourceGammaOneParabolicTateLift1409a.log', 'SourceGammaOnePicardFieldDefinition-1422.exit', 'SourceGammaOnePicardFieldDefinition-1422.log', 'SourceGammaOnePicardFieldDefinition.lean', 'SourceGammaOnePicardFieldDefinition1416a.exit', 'SourceGammaOnePicardFieldDefinition1416a.lean.txt', 'SourceGammaOnePicardFieldDefinition1416a.log', 'SourceGammaOnePicardFieldDefinition1416b.exit', 'SourceGammaOnePicardFieldDefinition1416b.lean', 'SourceGammaOnePicardFieldDefinition1416b.log', 'SourceGammaOnePlaceFieldDefinition-1422.exit', 'SourceGammaOnePlaceFieldDefinition-1422.log', 'SourceGammaOnePlaceFieldDefinition.lean', 'SourceGammaOnePlaceFieldDefinition1415a.exit', 'SourceGammaOnePlaceFieldDefinition1415a.lean', 'SourceGammaOnePlaceFieldDefinition1415a.log', 'SourceGammaOneTateOpenCongruence-1422.exit', 'SourceGammaOneTateOpenCongruence-1422.log', 'SourceGammaOneTateOpenCongruence.lean', 'SourceGammaOneTateOpenCongruence1417a.exit', 'SourceGammaOneTateOpenCongruence1417a.lean', 'SourceGammaOneTateOpenCongruence1417a.log', 'SourceGammaOneTwistedArithmeticDescent-1429.exit', 'SourceGammaOneTwistedArithmeticDescent-1429.log', 'SourceGammaOneTwistedArithmeticDescent.lean', 'SourceGammaOneTwistedArithmeticDescent1425a.exit', 'SourceGammaOneTwistedArithmeticDescent1425a.lean.txt', 'SourceGammaOneTwistedArithmeticDescent1425a.log', 'SourceGammaOneTwistedArithmeticDescent1425b.exit', 'SourceGammaOneTwistedArithmeticDescent1425b.lean.txt', 'SourceGammaOneTwistedArithmeticDescent1425b.log', 'SourceGammaOneTwistedArithmeticDescent1425c.exit', 'SourceGammaOneTwistedArithmeticDescent1425c.lean', 'SourceGammaOneTwistedArithmeticDescent1425c.log', 'SourceGammaOneTwistedAudit1.exit', 'SourceGammaOneTwistedAudit1.lean', 'SourceGammaOneTwistedAudit1.log', 'SourceGammaOneTwistedCongruence-1422.exit', 'SourceGammaOneTwistedCongruence-1422.log', 'SourceGammaOneTwistedCongruence.lean', 'SourceGammaOneTwistedCongruence1419a.exit', 'SourceGammaOneTwistedCongruence1419a.lean.txt', 'SourceGammaOneTwistedCongruence1419a.log', 'SourceGammaOneTwistedCongruence1419b.exit', 'SourceGammaOneTwistedCongruence1419b.lean', 'SourceGammaOneTwistedCongruence1419b.log', 'SourceGammaOneTwistedContinuity-1422.exit', 'SourceGammaOneTwistedContinuity-1422.log', 'SourceGammaOneTwistedContinuity.lean', 'SourceGammaOneTwistedContinuity1420a.exit', 'SourceGammaOneTwistedContinuity1420a.lean.txt', 'SourceGammaOneTwistedContinuity1420a.log', 'SourceGammaOneTwistedContinuity1420b.exit', 'SourceGammaOneTwistedContinuity1420b.lean.txt', 'SourceGammaOneTwistedContinuity1420b.log', 'SourceGammaOneTwistedContinuity1420c.exit', 'SourceGammaOneTwistedContinuity1420c.lean.txt', 'SourceGammaOneTwistedContinuity1420c.log', 'SourceGammaOneTwistedContinuity1420d.exit', 'SourceGammaOneTwistedContinuity1420d.lean.txt', 'SourceGammaOneTwistedContinuity1420d.log', 'SourceGammaOneTwistedContinuity1420e.exit', 'SourceGammaOneTwistedContinuity1420e.lean.txt', 'SourceGammaOneTwistedContinuity1420e.log', 'SourceGammaOneTwistedContinuity1420f.exit', 'SourceGammaOneTwistedContinuity1420f.lean', 'SourceGammaOneTwistedContinuity1420f.log', 'SourceGammaOneTwistedDependencyAudit1.exit', 'SourceGammaOneTwistedDependencyAudit1.lean', 'SourceGammaOneTwistedDependencyAudit1.log', 'SourceGammaOneTwistedFiniteFactor-1422.exit', 'SourceGammaOneTwistedFiniteFactor-1422.log', 'SourceGammaOneTwistedFiniteFactor.lean', 'SourceGammaOneTwistedFiniteFactor1421a.exit', 'SourceGammaOneTwistedFiniteFactor1421a.lean.txt', 'SourceGammaOneTwistedFiniteFactor1421a.log', 'SourceGammaOneTwistedFiniteFactor1421b.exit', 'SourceGammaOneTwistedFiniteFactor1421b.lean', 'SourceGammaOneTwistedFiniteFactor1421b.log', 'SourceGammaOneTwistedGalois-1411.exit', 'SourceGammaOneTwistedGalois-1411.log', 'SourceGammaOneTwistedGalois.lean', 'SourceGammaOneTwistedGalois1401a.lean.txt', 'SourceGammaOneTwistedGalois1401b.lean.txt', 'SourceGammaOneTwistedGalois1401c.exit', 'SourceGammaOneTwistedGalois1401c.lean.txt', 'SourceGammaOneTwistedGalois1401c.log', 'SourceGammaOneTwistedGalois1401d.exit', 'SourceGammaOneTwistedGalois1401d.lean.txt', 'SourceGammaOneTwistedGalois1401d.log', 'SourceGammaOneTwistedGalois1401e.exit', 'SourceGammaOneTwistedGalois1401e.lean', 'SourceGammaOneTwistedGalois1401e.log', 'SourceGammaOneTwistedGaloisDiamond-1429.exit', 'SourceGammaOneTwistedGaloisDiamond-1429.log', 'SourceGammaOneTwistedGaloisDiamond.lean', 'SourceGammaOneTwistedGaloisDiamond1427a.exit', 'SourceGammaOneTwistedGaloisDiamond1427a.lean', 'SourceGammaOneTwistedGaloisDiamond1427a.log', 'SourceGammaOneTwistedGaloisFrobenius-1411.exit', 'SourceGammaOneTwistedGaloisFrobenius-1411.log', 'SourceGammaOneTwistedGaloisFrobenius.lean', 'SourceGammaOneTwistedGaloisFrobenius1406a.exit', 'SourceGammaOneTwistedGaloisFrobenius1406a.lean.txt', 'SourceGammaOneTwistedGaloisFrobenius1406a.log', 'SourceGammaOneTwistedGaloisFrobenius1406b.exit', 'SourceGammaOneTwistedGaloisFrobenius1406b.lean.txt', 'SourceGammaOneTwistedGaloisFrobenius1406b.log', 'SourceGammaOneTwistedGaloisFrobenius1406c.exit', 'SourceGammaOneTwistedGaloisFrobenius1406c.lean.txt', 'SourceGammaOneTwistedGaloisFrobenius1406c.log', 'SourceGammaOneTwistedGaloisFrobenius1406d.exit', 'SourceGammaOneTwistedGaloisFrobenius1406d.lean', 'SourceGammaOneTwistedGaloisFrobenius1406d.log', 'SourceGammaOneTwistedGaloisHecke-1411.exit', 'SourceGammaOneTwistedGaloisHecke-1411.log', 'SourceGammaOneTwistedGaloisHecke.lean', 'SourceGammaOneTwistedGaloisHecke1404a.lean.txt', 'SourceGammaOneTwistedGaloisHecke1404b.exit', 'SourceGammaOneTwistedGaloisHecke1404b.lean', 'SourceGammaOneTwistedGaloisHecke1404b.log', 'SourceGammaOneTwistedGaloisInertia-1411.exit', 'SourceGammaOneTwistedGaloisInertia-1411.log', 'SourceGammaOneTwistedGaloisInertia.lean', 'SourceGammaOneTwistedGaloisInertia1408a.exit', 'SourceGammaOneTwistedGaloisInertia1408a.lean', 'SourceGammaOneTwistedGaloisInertia1408a.log', 'SourceGammaOneTwistedNormInertia-1429.exit', 'SourceGammaOneTwistedNormInertia-1429.log', 'SourceGammaOneTwistedNormInertia.lean', 'SourceGammaOneTwistedNormInertia1424a.exit', 'SourceGammaOneTwistedNormInertia1424a.lean.txt', 'SourceGammaOneTwistedNormInertia1424a.log', 'SourceGammaOneTwistedNormInertia1424b.exit', 'SourceGammaOneTwistedNormInertia1424b.lean', 'SourceGammaOneTwistedNormInertia1424b.log', 'SourceGammaOneTwistedScratchOwnership1412.exit', 'SourceGammaOneTwistedScratchOwnership1412.lean', 'SourceGammaOneTwistedScratchOwnership1412.log', 'SourceTwistedCoefficientDualAction-1411.exit', 'SourceTwistedCoefficientDualAction-1411.log', 'SourceTwistedCoefficientDualAction.lean', 'SourceTwistedCoefficientDualAction1398a.exit', 'SourceTwistedCoefficientDualAction1398a.lean', 'SourceTwistedCoefficientDualAction1398a.log', 'SourceTwistedCoefficientDualTrivial-1411.exit', 'SourceTwistedCoefficientDualTrivial-1411.log', 'SourceTwistedCoefficientDualTrivial.lean', 'SourceTwistedCoefficientDualTrivial1407a.exit', 'SourceTwistedCoefficientDualTrivial1407a.lean', 'SourceTwistedCoefficientDualTrivial1407a.log', 'audit_gamma_one_arithmetic_orbit_1430.ps1', 'audit_gamma_one_arithmetic_orbit_1430b.ps1', 'audit_gamma_one_continuity_1423.ps1', 'audit_gamma_one_twisted_1412.ps1', 'build_gamma_one_arithmetic_descent_1425.ps1', 'build_gamma_one_arithmetic_descent_1425b.ps1', 'build_gamma_one_arithmetic_descent_1425c.ps1', 'build_gamma_one_arithmetic_orbit_canonical_1429.ps1', 'build_gamma_one_continuity_canonical_1422.ps1', 'build_gamma_one_cyclotomic_hecke_1403a.ps1', 'build_gamma_one_cyclotomic_local_1405.ps1', 'build_gamma_one_finite_tate_dual_1418.ps1', 'build_gamma_one_finite_tate_dual_1418b.ps1', 'build_gamma_one_finite_tate_dual_1418c.ps1', 'build_gamma_one_function_definition_1413.ps1', 'build_gamma_one_galois_frobenius_1406b.ps1', 'build_gamma_one_galois_frobenius_1406d.ps1', 'build_gamma_one_galois_local_1407.ps1', 'build_gamma_one_global_coefficient_1399.ps1', 'build_gamma_one_norm_inertia_1424.ps1', 'build_gamma_one_norm_inertia_1424b.ps1', 'build_gamma_one_open_congruence_1417.ps1', 'build_gamma_one_parabolic_frobenius_1410.ps1', 'build_gamma_one_parabolic_frobenius_1410b.ps1', 'build_gamma_one_parabolic_galois_orbit_1428.ps1', 'build_gamma_one_parabolic_tate_1409.ps1', 'build_gamma_one_picard_definition_1416.ps1', 'build_gamma_one_picard_definition_1416b.ps1', 'build_gamma_one_place_definition_1415.ps1', 'build_gamma_one_place_orbit_1414.ps1', 'build_gamma_one_place_orbit_1414b.ps1', 'build_gamma_one_twisted_canonical_1411.ps1', 'build_gamma_one_twisted_congruence_1419.ps1', 'build_gamma_one_twisted_congruence_1419b.ps1', 'build_gamma_one_twisted_continuity_1420.ps1', 'build_gamma_one_twisted_continuity_1420b.ps1', 'build_gamma_one_twisted_continuity_1420c.ps1', 'build_gamma_one_twisted_continuity_1420d.ps1', 'build_gamma_one_twisted_continuity_1420e.ps1', 'build_gamma_one_twisted_continuity_1420f.ps1', 'build_gamma_one_twisted_diamond_1426.ps1', 'build_gamma_one_twisted_factor_1421.ps1', 'build_gamma_one_twisted_factor_1421b.ps1', 'build_gamma_one_twisted_galois_1401.ps1', 'build_gamma_one_twisted_galois_1401b.ps1', 'build_gamma_one_twisted_galois_1401c.ps1', 'build_gamma_one_twisted_galois_1401d.ps1', 'build_gamma_one_twisted_galois_1401e.ps1', 'build_gamma_one_twisted_hecke_1404.ps1', 'build_gamma_one_twisted_hecke_1404b.ps1', 'build_gamma_one_twisted_inertia_1408.ps1', 'build_gamma_one_twisted_trivial_1407.ps1', 'cohomology1401-focus.log', 'cohomology1401b-focus.log', 'cohomology1429a-focus.log', 'cohomology1429b-focus.log', 'cohomology1429c-focus.log', 'consumers1401-focus.log', 'consumers1401.txt', 'consumers1405-focus.log', 'consumers1405.txt', 'consumers1409-focus.log', 'consumers1409.txt', 'consumers1413-focus.log', 'consumers1413.txt', 'consumers1417-focus.log', 'consumers1417.txt', 'consumers1421-focus.log', 'consumers1421.txt', 'consumers1425-focus.log', 'consumers1425.txt', 'consumers1429-focus.log', 'consumers1429.txt', 'continuous1405-focus.log', 'continuous1405b-focus.log', 'continuous1405c-focus.log', 'continuous1405d-focus.log', 'continuous1405e-focus.log', 'continuous1405f-focus.log', 'continuous1405g-focus.log', 'continuous1405h-focus.log', 'continuous1405i-focus.log', 'continuous1405j-focus.log', 'continuous1405k-focus.log', 'continuous1405l-focus.log', 'continuous1405m-focus.log', 'continuous1405n-focus.log', 'coordinate1409a-focus.log', 'cotangent1421a-focus.log', 'cotangent1421b-focus.log', 'derivations1417a-focus.log', 'diagnose_gamma_one_galois_frobenius_1406c.ps1', 'diagnose_gamma_one_galois_frobenius_1406c.py', 'docs1401.py', 'docs1405.py', 'docs1409.py', 'docs1413.py', 'docs1417.py', 'docs1421.py', 'docs1425.py', 'docs1429.py', 'foundation1401-console.log', 'foundation1405-console.log', 'foundation1409-console.log', 'foundation1413-console.log', 'foundation1417-console.log', 'foundation1421-console.log', 'foundation1425-console.log', 'foundation1429-console.log', 'gamma-one-arithmetic-descent-reuse-1424.json', 'gamma-one-arithmetic-orbit-dependency-correction-1430b.json', 'gamma-one-arithmetic-orbit-versions-1429.json', 'gamma-one-continuity-reuse-1413.json', 'gamma-one-continuity-versions-1422.json', 'gamma-one-cyclotomic-local-reuse-1405.json', 'gamma-one-global-coefficient-route-1399.json', 'gamma-one-parabolic-tate-reuse-1409.json', 'gamma-one-tate-frobenius-promotion-route-1402.json', 'gamma-one-twisted-diamond-reuse-1426.json', 'gamma-one-twisted-factor-reuse-1421.json', 'gamma-one-twisted-versions-1411.json', 'gamma-one-unit-lift-reuse-1425.json', 'math1401.txt', 'math1405.txt', 'math1409.txt', 'math1413.txt', 'math1417.txt', 'math1421.txt', 'math1425.txt', 'math1429.txt', 'modules1401.json', 'modules1405.json', 'modules1409.json', 'modules1413.json', 'modules1417.json', 'modules1421.json', 'modules1425.json', 'modules1429.json', 'paper1401-console.log', 'paper1405-console.log', 'paper1409-console.log', 'paper1413-console.log', 'paper1417-console.log', 'paper1421-console.log', 'paper1425-console.log', 'paper1429-console.log', 'parameters1413a-focus.log', 'parameters1413b-focus.log', 'preflight1401.log', 'preflight1405.log', 'preflight1409.log', 'preflight1413.log', 'preflight1417.log', 'preflight1421.log', 'preflight1425.log', 'preflight1429.log', 'preflight1429b.log', 'preflight1429c.log', 'preflight1429d.log', 'prepare1401.py', 'prepare1405.py', 'prepare1409.py', 'prepare1413.py', 'prepare1417.py', 'prepare1421.py', 'prepare1425.py', 'prepare1429.py', 'prepare_gamma_one_arithmetic_descent_1425.py', 'prepare_gamma_one_arithmetic_orbit_audit_1430.py', 'prepare_gamma_one_arithmetic_orbit_audit_1430b.py', 'prepare_gamma_one_arithmetic_orbit_canonical_1429.py', 'prepare_gamma_one_arithmetic_orbit_dependency_1430b.py', 'prepare_gamma_one_continuity_audit_1423.py', 'prepare_gamma_one_continuity_canonical_1422.py', 'prepare_gamma_one_continuity_route_1413.py', 'prepare_gamma_one_cyclotomic_local_1405.py', 'prepare_gamma_one_finite_tate_dual_1418.py', 'prepare_gamma_one_galois_local_1407.py', 'prepare_gamma_one_global_coefficient_1399.py', 'prepare_gamma_one_norm_inertia_1424.py', 'prepare_gamma_one_open_congruence_1417.py', 'prepare_gamma_one_parabolic_frobenius_1410.py', 'prepare_gamma_one_parabolic_galois_orbit_1428.py', 'prepare_gamma_one_parabolic_tate_1409.py', 'prepare_gamma_one_picard_definition_1416.py', 'prepare_gamma_one_place_definition_1415.py', 'prepare_gamma_one_place_orbit_1414.py', 'prepare_gamma_one_tate_frobenius_1402.py', 'prepare_gamma_one_twisted_audit_1412.py', 'prepare_gamma_one_twisted_canonical_1411.py', 'prepare_gamma_one_twisted_congruence_1419.py', 'prepare_gamma_one_twisted_continuity_1420.py', 'prepare_gamma_one_twisted_diamond_1426.py', 'prepare_gamma_one_twisted_factor_1421.py', 'prepare_gamma_one_twisted_galois_1401.py', 'prepare_gamma_one_twisted_hecke_1404.py', 'prepare_gamma_one_twisted_inertia_1408.py', 'primary-review1401.json', 'primary-review1405.json', 'primary-review1409.json', 'primary-review1413.json', 'primary-review1417.json', 'primary-review1421.json', 'primary-review1425.json', 'primary-review1429.json', 'record1401.py', 'record1405.py', 'record1409.py', 'record1413.py', 'record1417.py', 'record1421.py', 'record1425.py', 'record1429.py', 'record_gamma_one_arithmetic_orbit_1430.py', 'record_gamma_one_arithmetic_orbit_1430b.py', 'record_gamma_one_continuity_1423.py', 'record_gamma_one_twisted_1412.py', 'register1401.py', 'register1405.py', 'register1409.py', 'register1413.py', 'register1417.py', 'register1421.py', 'register1425.py', 'register1429.py', 'registrations1401.json', 'registrations1405.json', 'registrations1409.json', 'registrations1413.json', 'registrations1417.json', 'registrations1421.json', 'registrations1425.json', 'registrations1429.json', 'remaining1401.txt', 'remaining1405.txt', 'remaining1409.txt', 'remaining1413.txt', 'remaining1417.txt', 'remaining1421.txt', 'remaining1425.txt', 'remaining1429.txt', 'repair_gamma_one_arithmetic_orbit_preparation_1430.py', 'revise_gamma_one_absolute_cyclotomic_1400b.py', 'revise_gamma_one_arithmetic_descent_1425b.py', 'revise_gamma_one_arithmetic_descent_1425c.py', 'revise_gamma_one_coefficient_diagonal_1399b.py', 'revise_gamma_one_finite_dual_1418b.py', 'revise_gamma_one_finite_dual_1418c.py', 'revise_gamma_one_galois_frobenius_1406b.py', 'revise_gamma_one_galois_frobenius_1406d.py', 'revise_gamma_one_norm_inertia_1424b.py', 'revise_gamma_one_picard_definition_1416b.py', 'revise_gamma_one_place_orbit_1414b.py', 'revise_gamma_one_twisted_congruence_1419b.py', 'revise_gamma_one_twisted_continuity_1420b.py', 'revise_gamma_one_twisted_continuity_1420c.py', 'revise_gamma_one_twisted_continuity_1420d.py', 'revise_gamma_one_twisted_continuity_1420e.py', 'revise_gamma_one_twisted_continuity_1420f.py', 'revise_gamma_one_twisted_factor_1421b.py', 'revise_gamma_one_twisted_galois_1401d.py', 'revise_gamma_one_twisted_galois_1401e.py', 'revise_gamma_one_twisted_hecke_1404b.py', 'revise_parabolic_frobenius_1410b.py', 'root1409-focus.log', 'root1413-focus.log', 'root1417-focus.log', 'root1421-focus.log', 'root1425-focus.log', 'root1429-focus.log', 'root1429b-focus.log', 'section1401.txt', 'section1405.txt', 'section1409.txt', 'section1413.txt', 'section1417.txt', 'section1421.txt', 'section1425.txt', 'section1429.txt', 'source-gamma-one-arithmetic-orbit-1-audit-config.json', 'source-gamma-one-arithmetic-orbit-2-audit-config.json', 'source-gamma-one-arithmetic-orbit-2-reuse-review-20261028.json', 'source-gamma-one-arithmetic-orbit-2-scratch-receipt.json', 'source-gamma-one-arithmetic-orbit-audit-route-1430.json', 'source-gamma-one-continuity-1-audit-config.json', 'source-gamma-one-continuity-1-reuse-review-20261028.json', 'source-gamma-one-continuity-1-scratch-receipt.json', 'source-gamma-one-continuity-audit-route-1423.json', 'source-gamma-one-twisted-1-audit-config.json', 'source-gamma-one-twisted-1-reuse-review-20261028.json', 'source-gamma-one-twisted-1-scratch-receipt.json', 'source-gamma-one-twisted-audit-route-1412.json', 'status1401.txt', 'status1405.txt', 'status1409.txt', 'status1413.txt', 'status1417.txt', 'status1421.txt', 'status1425.txt', 'status1429.txt', 'tangent1425a-focus.log', 'tangent1425b-focus.log']]
for folder in []:
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
    if source.suffix in ['.lean','.md']:target=target.with_name(target.name+'.txt')
    assert not target.exists(),target
    refresh_pending.append((target,source.read_bytes(),'Tools'))
    archive.append(dict(source=str(source),path=target.relative_to(r).as_posix(),sha256=sha(source)))
archive_target=r/archive_rel/'archive-manifest.json'
assert not archive_target.exists()
refresh_pending.append((archive_target,(json.dumps(dict(files=archive),indent=2)+'\n').encode(),'Tools'))
supplemental_review_path=r/archive_rel/'gamma-one-global-galois-promotion-route-1431.json'

audit = r / "Extension/Dubon2026/Audit.lean"
at = audit.read_text(encoding="utf-8")
for n in queries:
    assert not re.search(r"``" + re.escape(n) + r"(?=[,\s])", at)
tm, dm = "\n]\n\nprivate def publicConstructions", "\n]\n\nprivate def runAudit"
assert at.count(tm) == at.count(dm) == 1
at = at.replace(tm, "".join("\n  ,``" + n for n in theorems) + tm, 1)
at = at.replace(dm, "".join("\n  ," + chr(96)*2 + n for n in defs) + dm, 1)
research_path = r / "Tools/lean-reuse-audit-20261020.json"
reuse_path = r / "Tools/source-gamma-one-global-galois.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt9123"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> finite Gamma1 Hecke-character realization -> the actual continuous homogeneous-valued Tate Galois action, prescribed-support descent and original parabolic Frobenius polynomial.'
discharged = 'The actual cyclotomic character and original Picard Tate action now construct a genuine Galois representation on the finite homogeneous-valued Tate dual in every weight. Original finite fields of definition, open Picard stabilizers, uniform Tate congruences and the existing primitive-root continuity theorem prove continuity and a faithful finite Galois factor, without geometric degree/genus assumptions. Exact local cyclotomic values and the original norm-derived Tate relation give its Frobenius polynomial; the actual local inertia acts trivially when the original coordinate degree and genus are preserved. The existing continuous unit lift and prescribed-support quotient theorem then derive arithmetic descent from those two separate geometric families. The representation commutes with the actual good-prime Hecke and combined-diamond operators. The literal restriction of every original parabolic class has a Tate lift with derived combined-diamond fixedness, and the Frobenius polynomial holds throughout its Galois orbit in the existing comparison range 3<p. No continuity, finite Galois factor, unit lift, inertia identity, arithmetic descent, cyclotomic value, diamond fixedness or Frobenius relation is assumed in these consumers.'
boundary = 'Actual Gamma1 j-coordinate degree equality and genus preservation remain open and explicit in the local and arithmetic-descent consumers. The finite Tate-dual action and its faithful finite Galois factor do not yet give the required two-dimensional Hecke-character realization. Nonzero original parabolic character realization/transfer or a faithful alternative, exceptional coefficient primes, coefficient-field realization, original all-weight characteristic-zero association, local/image/regularity, automorphy and literal higher symmetric-power continuation remain. The parabolic Tate comparison retains 3<p; the continuity/finite-factor proof does not impose that restriction. The earlier differently normalized untwisted conditional relation is not claimed discharged. Acceptance stays 16/20; DUB-17--20 OPEN; all twenty acceptance tests are unchanged.'
status = 'The twenty-six-module scope passes 39 public axiom queries, 113 exhaustive scratch theorem checks, sixteen linters per module and three declaration-value audits with 80 required dependency checks, with zero diagnostics. Production aggregate, focused audits and sequential foundation/paper verification of the 9,149-module scope are pending.'
route = 'The October 28 upstream refresh and native proof search were checked before each dependency expansion. The actual homogeneous matrix representation, primitive-root cyclotomic character, original finite function/place/Picard fields, exact Tate projection kernel and period basis, native finite fixed-field theorem, adopted Imperial continuous unit lift, actual local valuation transport and original arithmetic quotient descent are reused. Original parabolic restriction and the proved Tate/H1 equivalence derive diamond fixedness; a minimal diagonal commutation gives its Galois stability. Generic narrow consumers resolve concrete elaboration costs without increasing proof limits. The full-H1 transfer surjectivity is not treated as parabolic transfer surjectivity. All promoted mathematical bodies and comments remain identical to their audited forms after import qualification; frozen sources, root pins and the owner-only BAT are unchanged.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Original Gamma One global Galois realization (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 9,123-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
corrections = []
count = sum(z['exhaustiveTheorems'] for z in certs)
assert count == 113

docpaths = list(dict.fromkeys(r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]))
for f in docpaths:
    assert "\n\n" in f.read_text(encoding="utf-8")
readmes = [(r.parent / "README.md", "Current Project 83 status ("), (repo / "README.md", "Project 83 has an ")]
for f, prefix in readmes:
    assert sum(line.startswith(prefix) for line in f.read_text(encoding="utf-8").splitlines()) == 1
arch = r / "Dubon Architecture.md"
edge = '  GAMMATATE9123["Original Gamma1 inertia and norm-derived Tate Frobenius from degree/genus equality; inverse-action homogeneous polynomial derived on combined-diamond fixed part. Actual degree/genus, global Galois/character realization and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourceGammaOneGlobalGaloisProductionAudit9149.lean',p/'source-gamma-one-global-galois-9149-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production9149.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/gamma-one-tate-frobenius-20261028-1402'
registered = {row['path'] for row in c['files']}
for priorFile in priorArchive.iterdir():
    rel = priorFile.relative_to(r).as_posix()
    if priorFile.is_file() and rel not in registered:
        c['files'].append({'path': rel, 'role': 'Tools'})

reportSource = p / 'Dubon Original Gamma One Global Galois Assessment 2026-10-28.md'
assert sha(reportSource) == '8E768055675F1857C44DC9221FDFB115B497B13BB9E0624278597A613F9B9975'
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
    "productionModules": 9149, "modules": newmods, "queries": queries,
    "theoremRegistrations": theorems, "constructionRegistrations": defs,
    "sourceHashes": {mapping[t.stem]: sha(t) for t, _ in pending}, "scratchCertificates": certs,
    "exactDependency": dependency, "assumptionsDischarged": discharged, "stillOpen": boundary,
    "status": status, "rootPinsChanged": False, "proofLimitsChanged": False,
    "promotionChanges": 'Only project scratch imports are qualified. All audited statements, proof bodies and comments remain identical. The original Gamma1 fields, actual homogeneous coefficients, cyclotomic character and Picard Tate action are retained. The local coordinate-degree/genus hypotheses and the parabolic comparison range are explicit; continuity and finite factorization impose no additional geometric hypothesis.',
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
arch.write_text(arch.read_text(encoding='utf-8').replace(edge,'  GAMMATATE9123["Original norm-derived Tate Frobenius and inertia from degree/genus equality (DUB-17/18)"] --> GAMMAGALOIS9149\n  GAMMAGALOIS9149["Actual finite homogeneous Tate Galois action: continuity and faithful finite factor proved; arithmetic descent and parabolic Galois-orbit Frobenius from degree/genus equality. Geometric equalities, nonzero character/two-dimensional realization and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'),encoding='utf-8')



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Original Gamma One global Galois realization - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-gamma-one-global-galois.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub('  logInfo m!".*"\n', '  logInfo m!"SOURCE GAMMA ONE GLOBAL GALOIS AUDIT PASS: {count} theorems including private/generated declarations. Actual continuous finite homogeneous Tate Galois action and faithful finite factor; original arithmetic descent and parabolic Galois-orbit Frobenius from coordinate-degree/genus equality. Actual geometric equalities and nonzero two-dimensional Hecke-character realization remain;16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourceGammaOneGlobalGaloisProductionAudit9149.lean").write_text(out, encoding="utf-8")
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
    target = p / (source.stem + "Production9149.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
(p / "source-gamma-one-global-galois-9149-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 9149, "increment": 26, "queries": 39,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
