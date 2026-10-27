from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 8554
assert d["appliedSourceGammaOnePeriodCharts"]["receipt8554"]["exit"] == 0
assert (p / "paper-verification-8554-console.exit").read_text().strip() == "0"
assert (r/'Tools/gamma-one-period-charts-20261026-709/canonical-evidence-8554.json').exists()
key = "appliedSourceGammaOneAnalyticOrbits"
assert key not in d
digests = {'source-gamma-one-analytic-integrality-3-scratch-receipt.json': 'DE02F3372BD9B59906C0789B6216036878E01A3DF7AE2521F76F5BBF01A4168D', 'source-gamma-one-finite-place-exhaustion-1-scratch-receipt.json': 'E6ABA2BC1900AF8FC78F2971B769058177725787F34615E098D407D9395ECCAB', 'source-gamma-one-place-invariance-2-scratch-receipt.json': 'CAF1D5DE07912D6B1048E62B935AD1CF75F04DB1020E5090992235289A3B7728', 'source-period-division-rotations-1-scratch-receipt.json': '6B135B560212A73DA7A79997FFD3D4F1FAB82AD0AF8196A78182D500D5BF0E59', 'source-gamma-one-division-forms-1-scratch-receipt.json': '67A2A455EA1489E8E70FA2DC6BB040EF75FABB413740476585EF12D6C27D32EE', 'source-gamma-one-division-lattice-orbit-1-scratch-receipt.json': '32FAE029F6C85A6674F82D0DBEC95FE5BF024878EB149827FCA22182DCDAC7D3', 'source-gamma-one-division-power-orbit-1-scratch-receipt.json': '96F84FF2A813BA0004ADD24646450143483EB550B8EDFAB31741F035D86AB39E', 'source-gamma-one-diamond-separation-1-scratch-receipt.json': '517813D4345F31C96A98B3DE808C4FBB79CEF3ECACA7FFC634392BBF885DA4CE', 'source-original-modular-point-separation-1-scratch-receipt.json': '98D205F22A03C26BA0175429CDAC130CDF4D7AE4436FEF1B1FD21BB747BB02C3', 'source-gamma-one-modular-point-separation-1-scratch-receipt.json': '1449BDB83A3C1E4D85CFA28BFE4891E0AA58D9078792D5E53DA8214389B4A432', 'source-gamma-one-normalized-cusp-ratios-1-scratch-receipt.json': '6FFE06FBAE7EFF5C61EBA4930EDCA9337CF676EE77C23DCFFE7078464B576D31', 'source-gamma-one-all-modular-ratio-membership-1-scratch-receipt.json': '9D7D4F6B76F1EB1A6EA9E70FF839B711879CF29E01627A2397B0D557956AD650', 'source-gamma-one-analytic-place-orbits-1-scratch-receipt.json': 'D52D4331D09869EB85F20229D34019F2F31B50432C198A4C689C2404B1E8D6B9', 'source-gamma-one-j-fiber-degree-1-scratch-receipt.json': '943E77399FF995F37355E06EDA98162D973C727DCB20B3E0B1495633042DACCE', 'source-gamma-one-orbit-counting-1-scratch-receipt.json': 'C89C2847D212987771C58DB12BFC1B2D9844DDB176D2ECFD35A0F149F85E9DC7', 'source-gamma-one-plus-minus-1-scratch-receipt.json': '773B88EB4C09248847B30BD0097C0179E1E282FC837E32BB8D1B2AA2E312960C', 'source-gamma-one-ramification-bounds-1-scratch-receipt.json': '1E199DC17E2C99AD8CD8BEF854D08DCC688B8C237435959B7B7BF3757AB06055', 'source-gamma-one-j-fiber-orbits-1-scratch-receipt.json': 'EF215FD0B404AB2A819AFEBF0F9D0DBD4061B8B10B7DB6F8AA39C5FDCCD412EB', 'source-gamma-one-generic-fiber-count-1-scratch-receipt.json': '111594BF58E3B4E90AF2CB9A96E24D70B2660283A3410EBA057CF22420CA2977'}

for name, digest in digests.items():
    assert sha(p / name) == digest
certs = [json.loads((p / name).read_text(encoding="utf-8")) for name in digests]
mods = [m for z in certs for m in z["modules"]]
queries = [q for z in certs for q in z["queries"]]
theorems = [q for z in certs for q in z["theoremRegistrations"]]
defs = [q for z in certs for q in z["constructionRegistrations"]]
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (22, 22, 62, 55, 7)
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
archive_rel='Tools/gamma-one-analytic-orbits-20261027-730'
evidence=[p/'gamma-one-analytic-orbits-promotion-route-730.json']
evidence += [p/n for n in ['SourceGammaOneAllModularRatioMembership.exit', 'SourceGammaOneAllModularRatioMembership.lean', 'SourceGammaOneAllModularRatioMembership.log', 'SourceGammaOneAllModularRatioMembershipAudit1.exit', 'SourceGammaOneAllModularRatioMembershipAudit1.lean', 'SourceGammaOneAllModularRatioMembershipAudit1.log', 'SourceGammaOneAllModularRatioMembershipDependencyAudit1.exit', 'SourceGammaOneAllModularRatioMembershipDependencyAudit1.lean', 'SourceGammaOneAllModularRatioMembershipDependencyAudit1.log', 'SourceGammaOneAllModularRatioMembershipScratchOwnership722.exit', 'SourceGammaOneAllModularRatioMembershipScratchOwnership722.lean', 'SourceGammaOneAllModularRatioMembershipScratchOwnership722.log', 'SourceGammaOneAnalyticIntegrality.exit', 'SourceGammaOneAnalyticIntegrality.lean', 'SourceGammaOneAnalyticIntegrality.log', 'SourceGammaOneAnalyticIntegralityAudit3.exit', 'SourceGammaOneAnalyticIntegralityAudit3.lean', 'SourceGammaOneAnalyticIntegralityAudit3.log', 'SourceGammaOneAnalyticIntegralityDependencyAudit3.exit', 'SourceGammaOneAnalyticIntegralityDependencyAudit3.lean', 'SourceGammaOneAnalyticIntegralityDependencyAudit3.log', 'SourceGammaOneAnalyticIntegralityScratchOwnership710.exit', 'SourceGammaOneAnalyticIntegralityScratchOwnership710.lean', 'SourceGammaOneAnalyticIntegralityScratchOwnership710.log', 'SourceGammaOneAnalyticPlaceInvariance.exit', 'SourceGammaOneAnalyticPlaceInvariance.lean', 'SourceGammaOneAnalyticPlaceInvariance.log', 'SourceGammaOneAnalyticPlaceOrbits.exit', 'SourceGammaOneAnalyticPlaceOrbits.lean', 'SourceGammaOneAnalyticPlaceOrbits.log', 'SourceGammaOneAnalyticPlaceOrbitsAudit1.exit', 'SourceGammaOneAnalyticPlaceOrbitsAudit1.lean', 'SourceGammaOneAnalyticPlaceOrbitsAudit1.log', 'SourceGammaOneAnalyticPlaceOrbitsDependencyAudit1.exit', 'SourceGammaOneAnalyticPlaceOrbitsDependencyAudit1.lean', 'SourceGammaOneAnalyticPlaceOrbitsDependencyAudit1.log', 'SourceGammaOneAnalyticPlaceOrbitsScratchOwnership723.exit', 'SourceGammaOneAnalyticPlaceOrbitsScratchOwnership723.lean', 'SourceGammaOneAnalyticPlaceOrbitsScratchOwnership723.log', 'SourceGammaOneDiamondSeparation.exit', 'SourceGammaOneDiamondSeparation.lean', 'SourceGammaOneDiamondSeparation.log', 'SourceGammaOneDiamondSeparationAudit1.exit', 'SourceGammaOneDiamondSeparationAudit1.lean', 'SourceGammaOneDiamondSeparationAudit1.log', 'SourceGammaOneDiamondSeparationDependencyAudit1.exit', 'SourceGammaOneDiamondSeparationDependencyAudit1.lean', 'SourceGammaOneDiamondSeparationDependencyAudit1.log', 'SourceGammaOneDiamondSeparationScratchOwnership718.exit', 'SourceGammaOneDiamondSeparationScratchOwnership718.lean', 'SourceGammaOneDiamondSeparationScratchOwnership718.log', 'SourceGammaOneDivisionForms.exit', 'SourceGammaOneDivisionForms.lean', 'SourceGammaOneDivisionForms.log', 'SourceGammaOneDivisionFormsAudit1.exit', 'SourceGammaOneDivisionFormsAudit1.lean', 'SourceGammaOneDivisionFormsAudit1.log', 'SourceGammaOneDivisionFormsDependencyAudit1.exit', 'SourceGammaOneDivisionFormsDependencyAudit1.lean', 'SourceGammaOneDivisionFormsDependencyAudit1.log', 'SourceGammaOneDivisionFormsScratchOwnership715.exit', 'SourceGammaOneDivisionFormsScratchOwnership715.lean', 'SourceGammaOneDivisionFormsScratchOwnership715.log', 'SourceGammaOneDivisionLatticeOrbit.exit', 'SourceGammaOneDivisionLatticeOrbit.lean', 'SourceGammaOneDivisionLatticeOrbit.log', 'SourceGammaOneDivisionLatticeOrbitAudit1.exit', 'SourceGammaOneDivisionLatticeOrbitAudit1.lean', 'SourceGammaOneDivisionLatticeOrbitAudit1.log', 'SourceGammaOneDivisionLatticeOrbitDependencyAudit1.exit', 'SourceGammaOneDivisionLatticeOrbitDependencyAudit1.lean', 'SourceGammaOneDivisionLatticeOrbitDependencyAudit1.log', 'SourceGammaOneDivisionLatticeOrbitScratchOwnership716.exit', 'SourceGammaOneDivisionLatticeOrbitScratchOwnership716.lean', 'SourceGammaOneDivisionLatticeOrbitScratchOwnership716.log', 'SourceGammaOneDivisionPowerOrbit.exit', 'SourceGammaOneDivisionPowerOrbit.lean', 'SourceGammaOneDivisionPowerOrbit.log', 'SourceGammaOneDivisionPowerOrbitAudit1.exit', 'SourceGammaOneDivisionPowerOrbitAudit1.lean', 'SourceGammaOneDivisionPowerOrbitAudit1.log', 'SourceGammaOneDivisionPowerOrbitDependencyAudit1.exit', 'SourceGammaOneDivisionPowerOrbitDependencyAudit1.lean', 'SourceGammaOneDivisionPowerOrbitDependencyAudit1.log', 'SourceGammaOneDivisionPowerOrbitScratchOwnership717.exit', 'SourceGammaOneDivisionPowerOrbitScratchOwnership717.lean', 'SourceGammaOneDivisionPowerOrbitScratchOwnership717.log', 'SourceGammaOneFinitePlaceExhaustion.exit', 'SourceGammaOneFinitePlaceExhaustion.lean', 'SourceGammaOneFinitePlaceExhaustion.log', 'SourceGammaOneFinitePlaceExhaustionAudit1.exit', 'SourceGammaOneFinitePlaceExhaustionAudit1.lean', 'SourceGammaOneFinitePlaceExhaustionAudit1.log', 'SourceGammaOneFinitePlaceExhaustionDependencyAudit1.exit', 'SourceGammaOneFinitePlaceExhaustionDependencyAudit1.lean', 'SourceGammaOneFinitePlaceExhaustionDependencyAudit1.log', 'SourceGammaOneFinitePlaceExhaustionScratchOwnership711.exit', 'SourceGammaOneFinitePlaceExhaustionScratchOwnership711.lean', 'SourceGammaOneFinitePlaceExhaustionScratchOwnership711.log', 'SourceGammaOneGenericFiberCount.exit', 'SourceGammaOneGenericFiberCount.lean', 'SourceGammaOneGenericFiberCount.log', 'SourceGammaOneGenericFiberCountAudit1.exit', 'SourceGammaOneGenericFiberCountAudit1.lean', 'SourceGammaOneGenericFiberCountAudit1.log', 'SourceGammaOneGenericFiberCountDependencyAudit1.exit', 'SourceGammaOneGenericFiberCountDependencyAudit1.lean', 'SourceGammaOneGenericFiberCountDependencyAudit1.log', 'SourceGammaOneGenericFiberCountScratchOwnership729.exit', 'SourceGammaOneGenericFiberCountScratchOwnership729.lean', 'SourceGammaOneGenericFiberCountScratchOwnership729.log', 'SourceGammaOneHolomorphicFunctions.exit', 'SourceGammaOneHolomorphicFunctions.lean', 'SourceGammaOneHolomorphicFunctions.log', 'SourceGammaOneJFiberDegree.exit', 'SourceGammaOneJFiberDegree.lean', 'SourceGammaOneJFiberDegree.log', 'SourceGammaOneJFiberDegreeAudit1.exit', 'SourceGammaOneJFiberDegreeAudit1.lean', 'SourceGammaOneJFiberDegreeAudit1.log', 'SourceGammaOneJFiberDegreeDependencyAudit1.exit', 'SourceGammaOneJFiberDegreeDependencyAudit1.lean', 'SourceGammaOneJFiberDegreeDependencyAudit1.log', 'SourceGammaOneJFiberDegreeScratchOwnership724.exit', 'SourceGammaOneJFiberDegreeScratchOwnership724.lean', 'SourceGammaOneJFiberDegreeScratchOwnership724.log', 'SourceGammaOneJFiberOrbits.exit', 'SourceGammaOneJFiberOrbits.lean', 'SourceGammaOneJFiberOrbits.log', 'SourceGammaOneJFiberOrbitsAudit1b.exit', 'SourceGammaOneJFiberOrbitsAudit1b.lean', 'SourceGammaOneJFiberOrbitsAudit1b.log', 'SourceGammaOneJFiberOrbitsDependencyAudit1b.exit', 'SourceGammaOneJFiberOrbitsDependencyAudit1b.lean', 'SourceGammaOneJFiberOrbitsDependencyAudit1b.log', 'SourceGammaOneJFiberOrbitsScratchOwnership728.exit', 'SourceGammaOneJFiberOrbitsScratchOwnership728.lean', 'SourceGammaOneJFiberOrbitsScratchOwnership728.log', 'SourceGammaOneModularPointSeparation.exit', 'SourceGammaOneModularPointSeparation.lean', 'SourceGammaOneModularPointSeparation.log', 'SourceGammaOneModularPointSeparationAudit1.exit', 'SourceGammaOneModularPointSeparationAudit1.lean', 'SourceGammaOneModularPointSeparationAudit1.log', 'SourceGammaOneModularPointSeparationDependencyAudit1.exit', 'SourceGammaOneModularPointSeparationDependencyAudit1.lean', 'SourceGammaOneModularPointSeparationDependencyAudit1.log', 'SourceGammaOneModularPointSeparationScratchOwnership720.exit', 'SourceGammaOneModularPointSeparationScratchOwnership720.lean', 'SourceGammaOneModularPointSeparationScratchOwnership720.log', 'SourceGammaOneNormalizedCuspRatios.exit', 'SourceGammaOneNormalizedCuspRatios.lean', 'SourceGammaOneNormalizedCuspRatios.log', 'SourceGammaOneNormalizedCuspRatiosAudit1.exit', 'SourceGammaOneNormalizedCuspRatiosAudit1.lean', 'SourceGammaOneNormalizedCuspRatiosAudit1.log', 'SourceGammaOneNormalizedCuspRatiosDependencyAudit1.exit', 'SourceGammaOneNormalizedCuspRatiosDependencyAudit1.lean', 'SourceGammaOneNormalizedCuspRatiosDependencyAudit1.log', 'SourceGammaOneNormalizedCuspRatiosScratchOwnership721.exit', 'SourceGammaOneNormalizedCuspRatiosScratchOwnership721.lean', 'SourceGammaOneNormalizedCuspRatiosScratchOwnership721.log', 'SourceGammaOneOrbitCounting.exit', 'SourceGammaOneOrbitCounting.lean', 'SourceGammaOneOrbitCounting.log', 'SourceGammaOneOrbitCountingAudit1.exit', 'SourceGammaOneOrbitCountingAudit1.lean', 'SourceGammaOneOrbitCountingAudit1.log', 'SourceGammaOneOrbitCountingDependencyAudit1.exit', 'SourceGammaOneOrbitCountingDependencyAudit1.lean', 'SourceGammaOneOrbitCountingDependencyAudit1.log', 'SourceGammaOneOrbitCountingScratchOwnership725.exit', 'SourceGammaOneOrbitCountingScratchOwnership725.lean', 'SourceGammaOneOrbitCountingScratchOwnership725.log', 'SourceGammaOnePlaceInvarianceAudit2.exit', 'SourceGammaOnePlaceInvarianceAudit2.lean', 'SourceGammaOnePlaceInvarianceAudit2.log', 'SourceGammaOnePlaceInvarianceDependencyAudit2.exit', 'SourceGammaOnePlaceInvarianceDependencyAudit2.lean', 'SourceGammaOnePlaceInvarianceDependencyAudit2.log', 'SourceGammaOnePlaceInvarianceScratchOwnership713.exit', 'SourceGammaOnePlaceInvarianceScratchOwnership713.lean', 'SourceGammaOnePlaceInvarianceScratchOwnership713.log', 'SourceGammaOnePlusMinus.exit', 'SourceGammaOnePlusMinus.lean', 'SourceGammaOnePlusMinus.log', 'SourceGammaOnePlusMinusAudit1b.exit', 'SourceGammaOnePlusMinusAudit1b.lean', 'SourceGammaOnePlusMinusAudit1b.log', 'SourceGammaOnePlusMinusDependencyAudit1b.exit', 'SourceGammaOnePlusMinusDependencyAudit1b.lean', 'SourceGammaOnePlusMinusDependencyAudit1b.log', 'SourceGammaOnePlusMinusScratchOwnership726.exit', 'SourceGammaOnePlusMinusScratchOwnership726.lean', 'SourceGammaOnePlusMinusScratchOwnership726.log', 'SourceGammaOneQuotientCuspSeries.exit', 'SourceGammaOneQuotientCuspSeries.lean', 'SourceGammaOneQuotientCuspSeries.log', 'SourceGammaOneRamificationBounds.exit', 'SourceGammaOneRamificationBounds.lean', 'SourceGammaOneRamificationBounds.log', 'SourceGammaOneRamificationBoundsAudit1.exit', 'SourceGammaOneRamificationBoundsAudit1.lean', 'SourceGammaOneRamificationBoundsAudit1.log', 'SourceGammaOneRamificationBoundsDependencyAudit1.exit', 'SourceGammaOneRamificationBoundsDependencyAudit1.lean', 'SourceGammaOneRamificationBoundsDependencyAudit1.log', 'SourceGammaOneRamificationBoundsScratchOwnership727.exit', 'SourceGammaOneRamificationBoundsScratchOwnership727.lean', 'SourceGammaOneRamificationBoundsScratchOwnership727.log', 'SourceGammaOneStabilizerRamification.exit', 'SourceGammaOneStabilizerRamification.lean', 'SourceGammaOneStabilizerRamification.log', 'SourceOriginalModularPointSeparation.exit', 'SourceOriginalModularPointSeparation.lean', 'SourceOriginalModularPointSeparation.log', 'SourceOriginalModularPointSeparationAudit1.exit', 'SourceOriginalModularPointSeparationAudit1.lean', 'SourceOriginalModularPointSeparationAudit1.log', 'SourceOriginalModularPointSeparationDependencyAudit1.exit', 'SourceOriginalModularPointSeparationDependencyAudit1.lean', 'SourceOriginalModularPointSeparationDependencyAudit1.log', 'SourceOriginalModularPointSeparationScratchOwnership719.exit', 'SourceOriginalModularPointSeparationScratchOwnership719.lean', 'SourceOriginalModularPointSeparationScratchOwnership719.log', 'SourcePeriodDivisionRotations.exit', 'SourcePeriodDivisionRotations.lean', 'SourcePeriodDivisionRotations.log', 'SourcePeriodDivisionRotationsAudit1.exit', 'SourcePeriodDivisionRotationsAudit1.lean', 'SourcePeriodDivisionRotationsAudit1.log', 'SourcePeriodDivisionRotationsDependencyAudit1.exit', 'SourcePeriodDivisionRotationsDependencyAudit1.lean', 'SourcePeriodDivisionRotationsDependencyAudit1.log', 'SourcePeriodDivisionRotationsScratchOwnership714.exit', 'SourcePeriodDivisionRotationsScratchOwnership714.lean', 'SourcePeriodDivisionRotationsScratchOwnership714.log', 'consumers715.txt', 'consumers718.txt', 'consumers723.txt', 'consumers729.txt', 'download_gamma_one_orbit_inputs_712.py', 'download_gamma_one_orbit_separation_712.py', 'foundation715-console.log', 'foundation718-console.log', 'foundation723-console.log', 'foundation729-console.log', 'gamma-one-all-modular-ratio-membership-audit-route-722.json', 'gamma-one-all-modular-ratio-membership-route-722.json', 'gamma-one-all-modular-ratio-membership-scratch-ownership-722.json', 'gamma-one-analytic-integrality-audit-route-710.json', 'gamma-one-analytic-integrality-route-710.json', 'gamma-one-analytic-integrality-scratch-ownership-710.json', 'gamma-one-analytic-place-orbits-audit-route-723.json', 'gamma-one-analytic-place-orbits-route-723.json', 'gamma-one-analytic-place-orbits-scratch-ownership-723.json', 'gamma-one-diamond-separation-audit-route-718.json', 'gamma-one-diamond-separation-route-718.json', 'gamma-one-diamond-separation-scratch-ownership-718.json', 'gamma-one-division-forms-audit-route-715.json', 'gamma-one-division-forms-route-715.json', 'gamma-one-division-forms-scratch-ownership-715.json', 'gamma-one-division-lattice-orbit-audit-route-716.json', 'gamma-one-division-lattice-orbit-route-716.json', 'gamma-one-division-lattice-orbit-scratch-ownership-716.json', 'gamma-one-division-power-orbit-audit-route-717.json', 'gamma-one-division-power-orbit-route-717.json', 'gamma-one-division-power-orbit-scratch-ownership-717.json', 'gamma-one-finite-place-exhaustion-audit-route-711.json', 'gamma-one-finite-place-exhaustion-route-711.json', 'gamma-one-finite-place-exhaustion-scratch-ownership-711.json', 'gamma-one-generic-fiber-count-audit-route-729.json', 'gamma-one-generic-fiber-count-route-729.json', 'gamma-one-generic-fiber-count-route-729b.json', 'gamma-one-generic-fiber-count-scratch-ownership-729.json', 'gamma-one-j-fiber-degree-audit-route-724.json', 'gamma-one-j-fiber-degree-route-724.json', 'gamma-one-j-fiber-degree-scratch-ownership-724.json', 'gamma-one-j-fiber-orbits-audit-route-728.json', 'gamma-one-j-fiber-orbits-route-728.json', 'gamma-one-j-fiber-orbits-scratch-ownership-728.json', 'gamma-one-modular-point-separation-audit-route-720.json', 'gamma-one-modular-point-separation-route-720.json', 'gamma-one-modular-point-separation-scratch-ownership-720.json', 'gamma-one-normalized-cusp-ratios-audit-route-721.json', 'gamma-one-normalized-cusp-ratios-route-721.json', 'gamma-one-normalized-cusp-ratios-scratch-ownership-721.json', 'gamma-one-orbit-counting-audit-route-725.json', 'gamma-one-orbit-counting-route-725.json', 'gamma-one-orbit-counting-scratch-ownership-725.json', 'gamma-one-place-invariance-audit-route-713.json', 'gamma-one-place-invariance-route-713.json', 'gamma-one-place-invariance-scratch-ownership-713.json', 'gamma-one-plus-minus-audit-route-726.json', 'gamma-one-plus-minus-route-726.json', 'gamma-one-plus-minus-scratch-ownership-726.json', 'gamma-one-ramification-bounds-audit-route-727.json', 'gamma-one-ramification-bounds-route-727.json', 'gamma-one-ramification-bounds-route-727b.json', 'gamma-one-ramification-bounds-scratch-ownership-727.json', 'modules715.json', 'modules718.json', 'modules723.json', 'modules729.json', 'original-modular-point-separation-audit-route-719.json', 'original-modular-point-separation-route-719.json', 'original-modular-point-separation-scratch-ownership-719.json', 'paper715-console.log', 'paper718-console.log', 'paper723-console.log', 'paper729-console.log', 'period-division-rotations-audit-route-714.json', 'period-division-rotations-route-714.json', 'period-division-rotations-scratch-ownership-714.json', 'prepare_gamma_one_all_modular_ratio_membership_audit_722.py', 'prepare_gamma_one_analytic_integrality_audit_710.py', 'prepare_gamma_one_analytic_place_orbits_audit_723.py', 'prepare_gamma_one_diamond_separation_audit_718.py', 'prepare_gamma_one_division_forms_audit_715.py', 'prepare_gamma_one_division_lattice_orbit_audit_716.py', 'prepare_gamma_one_division_power_orbit_audit_717.py', 'prepare_gamma_one_finite_place_exhaustion_audit_711.py', 'prepare_gamma_one_generic_fiber_count_audit_729.py', 'prepare_gamma_one_j_fiber_degree_audit_724.py', 'prepare_gamma_one_j_fiber_orbits_audit_728.py', 'prepare_gamma_one_modular_point_separation_audit_720.py', 'prepare_gamma_one_normalized_cusp_ratios_audit_721.py', 'prepare_gamma_one_orbit_counting_audit_725.py', 'prepare_gamma_one_place_invariance_audit_713.py', 'prepare_gamma_one_plus_minus_audit_726.py', 'prepare_gamma_one_ramification_bounds_audit_727.py', 'prepare_original_modular_point_separation_audit_719.py', 'prepare_original_modular_point_separation_recorder_719c.py', 'prepare_period_division_rotations_audit_714.py', 'record715.py', 'record718.py', 'record723.py', 'record729.py', 'record_gamma_one_all_modular_ratio_membership_722.py', 'record_gamma_one_analytic_integrality_710.py', 'record_gamma_one_analytic_place_orbits_723.py', 'record_gamma_one_diamond_separation_718.py', 'record_gamma_one_division_forms_715.py', 'record_gamma_one_division_lattice_orbit_716.py', 'record_gamma_one_division_power_orbit_717.py', 'record_gamma_one_finite_place_exhaustion_711.py', 'record_gamma_one_generic_fiber_count_729.py', 'record_gamma_one_j_fiber_degree_724.py', 'record_gamma_one_j_fiber_orbits_728.py', 'record_gamma_one_j_fiber_orbits_728b.py', 'record_gamma_one_modular_point_separation_720.py', 'record_gamma_one_normalized_cusp_ratios_721.py', 'record_gamma_one_orbit_counting_725.py', 'record_gamma_one_place_invariance_713.py', 'record_gamma_one_plus_minus_726.py', 'record_gamma_one_plus_minus_726b.py', 'record_gamma_one_ramification_bounds_727.py', 'record_original_modular_point_separation_719.py', 'record_period_division_rotations_714.py', 'register715.py', 'register718.py', 'register723.py', 'register729.py', 'registrations715.json', 'registrations718.json', 'registrations723.json', 'registrations729.json', 'section715.txt', 'section718.txt', 'section723.txt', 'section729.txt', 'source-gamma-one-all-modular-ratio-membership-1-audit-config.json', 'source-gamma-one-all-modular-ratio-membership-1-scratch-receipt.json', 'source-gamma-one-analytic-integrality-3-audit-config.json', 'source-gamma-one-analytic-integrality-3-scratch-receipt.json', 'source-gamma-one-analytic-place-orbits-1-audit-config.json', 'source-gamma-one-analytic-place-orbits-1-scratch-receipt.json', 'source-gamma-one-diamond-separation-1-audit-config.json', 'source-gamma-one-diamond-separation-1-scratch-receipt.json', 'source-gamma-one-division-forms-1-audit-config.json', 'source-gamma-one-division-forms-1-scratch-receipt.json', 'source-gamma-one-division-lattice-orbit-1-audit-config.json', 'source-gamma-one-division-lattice-orbit-1-scratch-receipt.json', 'source-gamma-one-division-power-orbit-1-audit-config.json', 'source-gamma-one-division-power-orbit-1-scratch-receipt.json', 'source-gamma-one-finite-place-exhaustion-1-audit-config.json', 'source-gamma-one-finite-place-exhaustion-1-scratch-receipt.json', 'source-gamma-one-generic-fiber-count-1-audit-config.json', 'source-gamma-one-generic-fiber-count-1-scratch-receipt.json', 'source-gamma-one-j-fiber-degree-1-audit-config.json', 'source-gamma-one-j-fiber-degree-1-scratch-receipt.json', 'source-gamma-one-j-fiber-orbits-1-audit-config.json', 'source-gamma-one-j-fiber-orbits-1-scratch-receipt.json', 'source-gamma-one-modular-point-separation-1-audit-config.json', 'source-gamma-one-modular-point-separation-1-scratch-receipt.json', 'source-gamma-one-normalized-cusp-ratios-1-audit-config.json', 'source-gamma-one-normalized-cusp-ratios-1-scratch-receipt.json', 'source-gamma-one-orbit-counting-1-audit-config.json', 'source-gamma-one-orbit-counting-1-scratch-receipt.json', 'source-gamma-one-place-invariance-2-audit-config.json', 'source-gamma-one-place-invariance-2-scratch-receipt.json', 'source-gamma-one-plus-minus-1-audit-config.json', 'source-gamma-one-plus-minus-1-scratch-receipt.json', 'source-gamma-one-plus-minus-1b-audit-config.json', 'source-gamma-one-ramification-bounds-1-audit-config.json', 'source-gamma-one-ramification-bounds-1-scratch-receipt.json', 'source-original-modular-point-separation-1-audit-config.json', 'source-original-modular-point-separation-1-scratch-receipt.json', 'source-period-division-rotations-1-audit-config.json', 'source-period-division-rotations-1-scratch-receipt.json', 'status715.txt', 'status718.txt', 'status723.txt', 'status729.txt', 'update715.py', 'update718.py', 'update723.py', 'update729.py']]
for folder in ['gamma-one-all-modular-ratio-membership-failed-722a', 'gamma-one-analytic-integrality-failed-710a', 'gamma-one-analytic-integrality-failed-710b', 'gamma-one-analytic-integrality-failed-710c', 'gamma-one-analytic-integrality-failed-710d', 'gamma-one-analytic-place-orbits-failed-723a', 'gamma-one-diamond-separation-failed-718a', 'gamma-one-diamond-separation-failed-718b', 'gamma-one-division-forms-failed-715a', 'gamma-one-division-lattice-orbit-failed-716a', 'gamma-one-division-power-orbit-failed-717a', 'gamma-one-division-power-orbit-failed-717b', 'gamma-one-finite-place-exhaustion-failed-711a', 'gamma-one-finite-place-exhaustion-failed-711b', 'gamma-one-finite-place-exhaustion-failed-711c', 'gamma-one-generic-fiber-count-failed-729a', 'gamma-one-j-fiber-orbits-failed-728a', 'gamma-one-normalized-cusp-ratios-failed-721a', 'gamma-one-normalized-cusp-ratios-failed-721b', 'gamma-one-orbit-separation-reuse-712', 'gamma-one-place-invariance-failed-713a', 'gamma-one-plus-minus-failed-726a', 'gamma-one-ramification-bounds-dependency-refresh-727c', 'gamma-one-ramification-bounds-failed-727a', 'gamma-one-ramification-bounds-failed-727b', 'original-modular-point-separation-audit-preparation-failed-719b', 'original-modular-point-separation-failed-719a', 'period-division-rotations-failed-714a']:
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
supplemental_review_path=r/archive_rel/'gamma-one-analytic-orbits-promotion-route-730.json'

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
reuse_path = r / "Tools/source-gamma-one-analytic-orbits.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt8554"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> arithmetic realization of original finite Gamma1 Hecke characters -> Picard/H1, full/parabolic, transpose and diamond comparison retaining the original homogeneous coefficient endomorphism -> actual global differential/cusp period geometry -> exact analytic-place orbit identification and finite-fiber ramification comparison.'
discharged = 'Regularity at every actual analytic place implies integrality over the original complex j line, and every finite place is realized by an actual upper-half-plane point. Native complex Gamma1 modular forms separate distinct Gamma1 orbits at every nonzero level, including elliptic points; their literal Fourier ratios lie in the original integral-ratio function field by the proved integral cusp spanning theorem. Consequently two actual analytic places are equal exactly on one Gamma1 orbit. The actual positive j fiber is in bijection with the corresponding subgroup orbits, with exact transport of place-order sums. Every finite fiber has the same total order, equal to the actual coordinate extension degree, and one genuine generic fiber has total order equal to the subgroup index. Actual uniformizer invariance and j multiplicity give the termwise ramification bound and its exact equality condition, with the central negative identity and required factor of two retained. No orbit dictionary, field membership, finite-place exhaustion, fiber bijection or degree identity is supplied as a hypothesis.'
boundary = 'The fixed-degree and generic-fiber sums must still be composed with the termwise bounds to prove exact elliptic ramification. Global Gamma1 charts, cusp charts and actual global period and Hecke/diamond/Picard/H1 comparison remain. These results do not close the arithmetic realization of original finite homogeneous-coefficient characters. Coefficient-field transport, Frobenius/inertia, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain. The full all-weight arithmetic goal is unchanged. Complex semisimplicity, finite characters, Witt coefficients and universal deformation rings do not supply a characteristic-zero lift or point. 16/20; DUB-17--20 OPEN.'
status = 'Actual Gamma1 finite-place exhaustion, exact analytic-place orbits and finite j-fiber comparisons pass 94 exhaustive scratch theorem checks and 62 public axiom queries across 22 modules, with sixteen linters per module and zero diagnostics. Nineteen declaration-value audits verify 156 required dependencies. Production aggregate, focused audit and sequential foundation/paper verification of the 8,576-module scope are pending.'
route = 'The renewed Lean reuse search supplies selected pinned Apache-2.0 division-form, orbit and ramification arguments. Shorter local routes reuse the existing Gamma0 integral-closure centers, integral Gamma1 cusp spanning, actual analytic representatives, positive-place-order degree sum and analytic j-surjectivity. Native modular-form powers and finite orbit-stabilizer APIs are consumed. No external import closure, new coefficient field, repeated rational-function comparison framework or separate 2*i fundamental-domain calculation is introduced. Only audited mathematical sources are promoted and only imports are qualified. Failed variants, audit classifications and all predecessor evidence remain preserved. Pins, proof limits, frozen paper and all twenty acceptance gates are unchanged.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Actual Gamma1 analytic-place orbits and finite fibers (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 8,554-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
corrections = []
count = sum(z['exhaustiveTheorems'] for z in certs)
assert count == 94

docpaths = list(dict.fromkeys(r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]))
for f in docpaths:
    assert "\n\n" in f.read_text(encoding="utf-8")
readmes = [(r.parent / "README.md", "Current Project 83 status ("), (repo / "README.md", "Project 83 has an ")]
for f, prefix in readmes:
    assert sum(line.startswith(prefix) for line in f.read_text(encoding="utf-8").splitlines()) == 1
arch = r / "Dubon Architecture.md"
edge = '  GAMMAONEPERIOD8554["Exact differential integrand, actual residue comparison and unramified local charts proved. Elliptic/global charts, period/Hecke/diamond/Picard/H1, all-weight arithmetic association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourceGammaOneAnalyticOrbitsProductionAudit8576.lean',p/'source-gamma-one-analytic-orbits-8576-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production8576.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/gamma-one-period-charts-20261026-709'
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
    "productionModules": 8576, "modules": newmods, "queries": queries,
    "theoremRegistrations": theorems, "constructionRegistrations": defs,
    "sourceHashes": {mapping[t.stem]: sha(t) for t, _ in pending}, "scratchCertificates": certs,
    "exactDependency": dependency, "assumptionsDischarged": discharged, "stillOpen": boundary,
    "status": status, "rootPinsChanged": False, "proofLimitsChanged": False,
    "promotionChanges": 'Only scratch imports are qualified. All final audited statements, proof bodies and comments remain identical. Actual integral-ratio fields, native modular forms, literal Fourier series, analytic places and exact fiber multiplicities are retained. No source contract is weakened.',
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
arch.write_text(arch.read_text(encoding='utf-8').replace(edge,'  GAMMAONEPERIOD8554["Exact differential integrand, actual residue comparison and unramified local charts (DUB-17/18)"] --> GAMMAONEORBITS8576\n  GAMMAONEORBITS8576["Actual Gamma1 finite-place exhaustion, exact analytic-place orbits and finite j-fiber bijections proved. Exact elliptic ramification/global charts, period/Hecke/diamond/Picard/H1, all-weight arithmetic association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'),encoding='utf-8')



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Actual Gamma1 analytic-place orbits and finite fibers - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-gamma-one-analytic-orbits.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub('  logInfo m!".*"\n', '  logInfo m!"SOURCE GAMMA ONE ANALYTIC ORBITS AUDIT PASS: {count} theorems including private/generated declarations. Actual finite-place exhaustion, exact Gamma1 analytic-place orbits, integral-ratio membership and finite j-fiber comparisons are proved. Composition to exact elliptic ramification and global chart/period obligations remains. Original Hecke/diamond/Picard/H1 arithmetic comparison remains; 16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourceGammaOneAnalyticOrbitsProductionAudit8576.lean").write_text(out, encoding="utf-8")
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
    target = p / (source.stem + "Production8576.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
(p / "source-gamma-one-analytic-orbits-8576-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 8576, "increment": 22, "queries": 62,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
