from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 8721
assert d["appliedSourceGammaOneSmoothComparison"]["receipt8721"]["exit"] == 0
assert (p / "paper-verification-8721-console.exit").read_text().strip() == "0"
assert (r/'Tools/gamma-one-smooth-comparison-20261027-894/canonical-evidence-8721.json').exists()
key = "appliedSourceGammaOneDivisorReciprocity"
assert key not in d
digests = {'source-gamma-one-smooth-divisor-1b-scratch-receipt.json': 'E1FED85BC3E76CF4CE3D0395F754205F4E0405D0B8059F2E4A709CE6084B9897', 'source-gamma-one-smooth-divisor-period-1b-scratch-receipt.json': 'AFA3D58464D6BA1438DD115F2DCC7A02B7B5F1C48F27AC0EE87184233A8C706C', 'source-gamma-one-divisor-winding-1-scratch-receipt.json': '25E989665DF46ED0A363578B879EA4E96AD9ADDDF4E724191C97F8B1B2724899', 'source-modular-green-boundary-1-scratch-receipt.json': '37818972A1262AFF7EF31631ACA869239D3F2B061511260F609C2F50AB023567', 'source-original-divisor-winding-boundary-1-scratch-receipt.json': 'FE3580B611787E70DF7DF3758E97101F67D95ABE86AEB2043BCFCC6B29A397C5', 'source-original-winding-integral-period-1b-scratch-receipt.json': '2B8EB76B77A496A6BA79B45DD5FE9CD1A6714C64A3FC4407E55FA83BBB1F2CAB', 'source-original-petersson-reciprocity-1-scratch-receipt.json': '72BB2D8192FFB646DBBA2588D643F00DEBAD7F0CC78CB20BF4AE616EE4FBA05F'}

for name, digest in digests.items():
    assert sha(p / name) == digest
certs = [json.loads((p / name).read_text(encoding="utf-8")) for name in digests]
mods = [m for z in certs for m in z["modules"]]
queries = [q for z in certs for q in z["queries"]]
theorems = [q for z in certs for q in z["theoremRegistrations"]]
defs = [q for z in certs for q in z["constructionRegistrations"]]
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (55, 55, 341, 308, 33)
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
archive_rel='Tools/gamma-one-divisor-reciprocity-20261027-951'
evidence=[p/'gamma-one-divisor-reciprocity-promotion-route-951.json']
evidence += [p/n for n in ['SourceComplexHolomorphicStokes.lean', 'SourceFinitePermutationCoboundary.lean', 'SourceFinitePermutationCoboundary937a.exit', 'SourceFinitePermutationCoboundary937a.log', 'SourceGammaOneDivisorWindingAudit1.exit', 'SourceGammaOneDivisorWindingAudit1.lean', 'SourceGammaOneDivisorWindingAudit1.log', 'SourceGammaOneDivisorWindingBoundary.lean', 'SourceGammaOneDivisorWindingBoundary933a.exit', 'SourceGammaOneDivisorWindingBoundary933a.log', 'SourceGammaOneDivisorWindingComparison.lean', 'SourceGammaOneDivisorWindingComparison918a.exit', 'SourceGammaOneDivisorWindingComparison918a.log', 'SourceGammaOneDivisorWindingComparison918b.exit', 'SourceGammaOneDivisorWindingComparison918b.log', 'SourceGammaOneDivisorWindingDependencyAudit1.exit', 'SourceGammaOneDivisorWindingDependencyAudit1.lean', 'SourceGammaOneDivisorWindingDependencyAudit1.log', 'SourceGammaOneDivisorWindingIntegralPeriod.lean', 'SourceGammaOneDivisorWindingIntegralPeriod941a.exit', 'SourceGammaOneDivisorWindingIntegralPeriod941a.log', 'SourceGammaOneDivisorWindingIntegralPeriod941b.exit', 'SourceGammaOneDivisorWindingIntegralPeriod941b.log', 'SourceGammaOneDivisorWindingIntegralPeriod941c.exit', 'SourceGammaOneDivisorWindingIntegralPeriod941c.log', 'SourceGammaOneDivisorWindingScratchOwnership919.exit', 'SourceGammaOneDivisorWindingScratchOwnership919.lean', 'SourceGammaOneDivisorWindingScratchOwnership919.log', 'SourceGammaOnePeterssonReciprocity.lean', 'SourceGammaOnePeterssonReciprocity948a.exit', 'SourceGammaOnePeterssonReciprocity948a.log', 'SourceGammaOnePeterssonSmoothLimit.lean', 'SourceGammaOneSmoothDivisorAudit1b.exit', 'SourceGammaOneSmoothDivisorAudit1b.lean', 'SourceGammaOneSmoothDivisorAudit1b.log', 'SourceGammaOneSmoothDivisorComparison.lean', 'SourceGammaOneSmoothDivisorComparison906a.exit', 'SourceGammaOneSmoothDivisorComparison906a.log', 'SourceGammaOneSmoothDivisorComparison908a.exit', 'SourceGammaOneSmoothDivisorComparison908a.log', 'SourceGammaOneSmoothDivisorDependencyAudit1b.exit', 'SourceGammaOneSmoothDivisorDependencyAudit1b.lean', 'SourceGammaOneSmoothDivisorDependencyAudit1b.log', 'SourceGammaOneSmoothDivisorPeriodAudit1.exit', 'SourceGammaOneSmoothDivisorPeriodAudit1.lean', 'SourceGammaOneSmoothDivisorPeriodAudit1.log', 'SourceGammaOneSmoothDivisorPeriodDependencyAudit1b.exit', 'SourceGammaOneSmoothDivisorPeriodDependencyAudit1b.lean', 'SourceGammaOneSmoothDivisorPeriodDependencyAudit1b.log', 'SourceGammaOneSmoothDivisorPeriodIntegral.lean', 'SourceGammaOneSmoothDivisorPeriodIntegral913a.exit', 'SourceGammaOneSmoothDivisorPeriodIntegral913a.log', 'SourceGammaOneSmoothDivisorPeriodScratchOwnership914.exit', 'SourceGammaOneSmoothDivisorPeriodScratchOwnership914.lean', 'SourceGammaOneSmoothDivisorPeriodScratchOwnership914.log', 'SourceGammaOneSmoothDivisorScratchOwnership909b.exit', 'SourceGammaOneSmoothDivisorScratchOwnership909b.lean', 'SourceGammaOneSmoothDivisorScratchOwnership909b.log', 'SourceGammaOneSmoothDivisorValueProbe907.exit', 'SourceGammaOneSmoothDivisorValueProbe907.log', 'SourceGammaOneSmoothedReciprocity.lean', 'SourceGammaOneSmoothedReciprocity946a.exit', 'SourceGammaOneSmoothedReciprocity946a.log', 'SourceMeromorphicUntwistDerivative.lean', 'SourceModularBoundarySidePairing.lean', 'SourceModularBoundarySidePairing921a.exit', 'SourceModularBoundarySidePairing921a.log', 'SourceModularCuspBoundaryDecay.lean', 'SourceModularCuspBoundaryDecay924a.exit', 'SourceModularCuspBoundaryDecay924a.log', 'SourceModularCuspBoundaryDecay924b.exit', 'SourceModularCuspBoundaryDecay924b.log', 'SourceModularGreenArc.lean', 'SourceModularGreenArc922a.exit', 'SourceModularGreenArc922a.log', 'SourceModularGreenBoundaryAudit1.exit', 'SourceModularGreenBoundaryAudit1.lean', 'SourceModularGreenBoundaryAudit1.log', 'SourceModularGreenBoundaryDependencyAudit1.exit', 'SourceModularGreenBoundaryDependencyAudit1.lean', 'SourceModularGreenBoundaryDependencyAudit1.log', 'SourceModularGreenBoundaryScratchOwnership925.exit', 'SourceModularGreenBoundaryScratchOwnership925.lean', 'SourceModularGreenBoundaryScratchOwnership925.log', 'SourceModularGreenBoundaryValueProbe923.exit', 'SourceModularGreenBoundaryValueProbe923.log', 'SourceModularGreenDensity.lean', 'SourceModularGreenDensity928a.exit', 'SourceModularGreenDensity928a.log', 'SourceModularGreenDomain.lean', 'SourceModularGreenDomain922a.exit', 'SourceModularGreenDomain922a.log', 'SourceModularGreenEdges.lean', 'SourceModularGreenEdges926c.exit', 'SourceModularGreenEdges926c.log', 'SourceModularGreenFormula.lean', 'SourceModularGreenFormula922a.exit', 'SourceModularGreenFormula922a.log', 'SourceModularGreenLines.lean', 'SourceModularGreenLines922a.exit', 'SourceModularGreenLines922a.log', 'SourceModularGreenMeasure.lean', 'SourceModularGreenMeasure927a.exit', 'SourceModularGreenMeasure927a.log', 'SourceModularGreenMeasure927b.exit', 'SourceModularGreenMeasure927b.log', 'SourceModularGreenPullback.lean', 'SourceModularGreenPullback926a.exit', 'SourceModularGreenPullback926a.log', 'SourceModularGreenPullback926b.exit', 'SourceModularGreenPullback926b.log', 'SourceModularGreenSidePairing.lean', 'SourceModularGreenSidePairing929a.exit', 'SourceModularGreenSidePairing929a.log', 'SourceModularGreenSliceGeometry.lean', 'SourceModularGreenSliceGeometry922a.exit', 'SourceModularGreenSliceGeometry922a.log', 'SourceModularGreenSlicing.lean', 'SourceModularGreenSlicing922a.exit', 'SourceModularGreenSlicing922a.log', 'SourceModularGreenTile.lean', 'SourceModularGreenTile926b.exit', 'SourceModularGreenTile926b.log', 'SourceModularGreenTile926c.exit', 'SourceModularGreenTile926c.log', 'SourceModularPeriodCorners.lean', 'SourceModularPeriodCorners938c.exit', 'SourceModularPeriodCorners938c.log', 'SourceModularPeriodCorners938d.exit', 'SourceModularPeriodCorners938d.log', 'SourceModularPeriodCorners938e.exit', 'SourceModularPeriodCorners938e.log', 'SourceModularSidePairingAction.lean', 'SourceModularSidePairingAction920a.exit', 'SourceModularSidePairingAction920a.log', 'SourceModularSidePairingAction920b.exit', 'SourceModularSidePairingAction920b.log', 'SourceModularSidePairingIntegrals.lean', 'SourceModularSidePairingIntegrals921a.exit', 'SourceModularSidePairingIntegrals921a.log', 'SourceModularSmoothProjectiveRepresentatives.lean', 'SourceModularSmoothProjectiveRepresentatives895a.exit', 'SourceModularSmoothProjectiveRepresentatives895a.log', 'SourceModularSmoothProjectiveRepresentatives895b.exit', 'SourceModularSmoothProjectiveRepresentatives895b.log', 'SourceModularSmoothProjectiveRepresentatives908a.exit', 'SourceModularSmoothProjectiveRepresentatives908a.log', 'SourceModularSmoothProjectiveRepresentatives908b.exit', 'SourceModularSmoothProjectiveRepresentatives908b.log', 'SourceModularSmoothedGreenLimit.lean', 'SourceModularSmoothedGreenLimit931a.exit', 'SourceModularSmoothedGreenLimit931a.log', 'SourceModularSmoothedGreenLimit931b.exit', 'SourceModularSmoothedGreenLimit931b.log', 'SourceModularSmoothedGreenLimit931c.exit', 'SourceModularSmoothedGreenLimit931c.log', 'SourceModularSmoothedGreenLimit931d.exit', 'SourceModularSmoothedGreenLimit931d.log', 'SourceOriginalDivisorWindingBoundaryAudit1.exit', 'SourceOriginalDivisorWindingBoundaryAudit1.lean', 'SourceOriginalDivisorWindingBoundaryAudit1.log', 'SourceOriginalDivisorWindingBoundaryDependencyAudit1.exit', 'SourceOriginalDivisorWindingBoundaryDependencyAudit1.lean', 'SourceOriginalDivisorWindingBoundaryDependencyAudit1.log', 'SourceOriginalDivisorWindingBoundaryScratchOwnership935.exit', 'SourceOriginalDivisorWindingBoundaryScratchOwnership935.lean', 'SourceOriginalDivisorWindingBoundaryScratchOwnership935.log', 'SourceOriginalDivisorWindingBoundaryValueProbe934.exit', 'SourceOriginalDivisorWindingBoundaryValueProbe934.log', 'SourceOriginalPeterssonReciprocityAudit1.exit', 'SourceOriginalPeterssonReciprocityAudit1.lean', 'SourceOriginalPeterssonReciprocityAudit1.log', 'SourceOriginalPeterssonReciprocityDependencyAudit1.exit', 'SourceOriginalPeterssonReciprocityDependencyAudit1.lean', 'SourceOriginalPeterssonReciprocityDependencyAudit1.log', 'SourceOriginalPeterssonReciprocityScratchOwnership950.exit', 'SourceOriginalPeterssonReciprocityScratchOwnership950.lean', 'SourceOriginalPeterssonReciprocityScratchOwnership950.log', 'SourceOriginalPeterssonReciprocityValueProbe949.exit', 'SourceOriginalPeterssonReciprocityValueProbe949.lean', 'SourceOriginalPeterssonReciprocityValueProbe949.log', 'SourceOriginalWindingIntegralPeriodAudit1b.exit', 'SourceOriginalWindingIntegralPeriodAudit1b.lean', 'SourceOriginalWindingIntegralPeriodAudit1b.log', 'SourceOriginalWindingIntegralPeriodDependencyAudit1b.exit', 'SourceOriginalWindingIntegralPeriodDependencyAudit1b.lean', 'SourceOriginalWindingIntegralPeriodDependencyAudit1b.log', 'SourceOriginalWindingIntegralPeriodScratchOwnership943b.exit', 'SourceOriginalWindingIntegralPeriodScratchOwnership943b.lean', 'SourceOriginalWindingIntegralPeriodScratchOwnership943b.log', 'SourceOriginalWindingIntegralPeriodValueProbe942.exit', 'SourceOriginalWindingIntegralPeriodValueProbe942.lean', 'SourceOriginalWindingIntegralPeriodValueProbe942.log', 'SourceParabolicCosetPotentials.lean', 'SourceParabolicCosetPotentials937a.exit', 'SourceParabolicCosetPotentials937a.log', 'SourceParabolicCosetPotentials937b.exit', 'SourceParabolicCosetPotentials937b.log', 'SourceParabolicCosetPotentials937c.exit', 'SourceParabolicCosetPotentials937c.log', 'SourceParabolicWindingIntegralPeriods.lean', 'SourceParabolicWindingIntegralPeriods940a.exit', 'SourceParabolicWindingIntegralPeriods940a.log', 'SourceParabolicWindingIntegralPeriods940b.exit', 'SourceParabolicWindingIntegralPeriods940b.log', 'SourceSmoothCompactTranslateIntegral.lean', 'SourceSmoothCompactTranslateIntegral911a.exit', 'SourceSmoothCompactTranslateIntegral911a.log', 'SourceSmoothCompactTranslateIntegral911b.exit', 'SourceSmoothCompactTranslateIntegral911b.log', 'SourceSmoothComparisonCusps.lean', 'SourceSmoothComparisonCusps916a.exit', 'SourceSmoothComparisonCusps916a.log', 'SourceSmoothComparisonDbar.lean', 'SourceSmoothComparisonDbar944a.exit', 'SourceSmoothComparisonDbar944a.log', 'SourceSmoothComparisonDbar944b.exit', 'SourceSmoothComparisonDbar944b.log', 'SourceSmoothComparisonQuotient.lean', 'SourceSmoothComparisonQuotient915a.exit', 'SourceSmoothComparisonQuotient915a.log', 'SourceSmoothComparisonWindingLog.lean', 'SourceSmoothComparisonWindingLog917a.exit', 'SourceSmoothComparisonWindingLog917a.log', 'SourceSmoothDivisorInvarianceCusps.lean', 'SourceSmoothDivisorInvarianceCusps903a.exit', 'SourceSmoothDivisorInvarianceCusps903a.log', 'SourceSmoothDivisorInvarianceCusps908a.exit', 'SourceSmoothDivisorInvarianceCusps908a.log', 'SourceSmoothDivisorLocalOrders.lean', 'SourceSmoothDivisorLocalOrders902a.exit', 'SourceSmoothDivisorLocalOrders902a.log', 'SourceSmoothDivisorLocalOrders908a.exit', 'SourceSmoothDivisorLocalOrders908a.log', 'SourceSmoothDivisorLocalProduct.lean', 'SourceSmoothDivisorLocalProduct901a.exit', 'SourceSmoothDivisorLocalProduct901a.log', 'SourceSmoothDivisorLocalProduct901b.exit', 'SourceSmoothDivisorLocalProduct901b.log', 'SourceSmoothDivisorLocalProduct908a.exit', 'SourceSmoothDivisorLocalProduct908a.log', 'SourceSmoothDivisorLogDerivative.lean', 'SourceSmoothDivisorLogDerivative904a.exit', 'SourceSmoothDivisorLogDerivative904a.log', 'SourceSmoothDivisorLogDerivative904b.exit', 'SourceSmoothDivisorLogDerivative904b.log', 'SourceSmoothDivisorLogDerivative908a.exit', 'SourceSmoothDivisorLogDerivative908a.log', 'SourceSmoothDivisorOrbitData.lean', 'SourceSmoothDivisorOrbitData898a.exit', 'SourceSmoothDivisorOrbitData898a.log', 'SourceSmoothDivisorOrbitData898b.exit', 'SourceSmoothDivisorOrbitData898b.log', 'SourceSmoothDivisorOrbitData908a.exit', 'SourceSmoothDivisorOrbitData908a.log', 'SourceSmoothDivisorPeriodIntegral.lean', 'SourceSmoothDivisorPeriodIntegral912a.exit', 'SourceSmoothDivisorPeriodIntegral912a.log', 'SourceSmoothDivisorPeriodIntegral912b.exit', 'SourceSmoothDivisorPeriodIntegral912b.log', 'SourceSmoothDivisorProduct.lean', 'SourceSmoothDivisorProduct900a.exit', 'SourceSmoothDivisorProduct900a.log', 'SourceSmoothDivisorProduct900b.exit', 'SourceSmoothDivisorProduct900b.log', 'SourceSmoothDivisorProduct908a.exit', 'SourceSmoothDivisorProduct908a.log', 'SourceSmoothInvariantComparison.lean', 'SourceSmoothInvariantComparison905a.exit', 'SourceSmoothInvariantComparison905a.log', 'SourceSmoothInvariantComparison908a.exit', 'SourceSmoothInvariantComparison908a.log', 'SourceSmoothLocalModelProducts.lean', 'SourceSmoothLocalModelProducts892a.exit', 'SourceSmoothLocalModelProducts892a.log', 'SourceSmoothLocalModelRegularization.lean', 'SourceSmoothLocalModelRegularization892a.exit', 'SourceSmoothLocalModelRegularization892a.log', 'SourceSmoothModularGeometry.lean', 'SourceSmoothModularGeometry896a.exit', 'SourceSmoothModularGeometry896a.log', 'SourceSmoothModularGeometry896b.exit', 'SourceSmoothModularGeometry896b.log', 'SourceSmoothModularGeometry908a.exit', 'SourceSmoothModularGeometry908a.log', 'SourceSmoothModularLogDerivative.lean', 'SourceSmoothModularLogDerivative899a.exit', 'SourceSmoothModularLogDerivative899a.log', 'SourceSmoothModularLogDerivative899b.exit', 'SourceSmoothModularLogDerivative899b.log', 'SourceSmoothModularLogDerivative899c.exit', 'SourceSmoothModularLogDerivative899c.log', 'SourceSmoothModularLogDerivative908a.exit', 'SourceSmoothModularLogDerivative908a.log', 'SourceSmoothOrbitIntegralChangeVariables.lean', 'SourceSmoothOrbitIntegralChangeVariables910a.exit', 'SourceSmoothOrbitIntegralChangeVariables910a.log', 'SourceSmoothOrbitIntegralChangeVariables910b.exit', 'SourceSmoothOrbitIntegralChangeVariables910b.log', 'SourceSmoothOrbitIntegralChangeVariables910c.exit', 'SourceSmoothOrbitIntegralChangeVariables910c.log', 'SourceSmoothOrbitIntegralGeometry.lean', 'SourceSmoothOrbitIntegralGeometry910a.exit', 'SourceSmoothOrbitIntegralGeometry910a.log', 'SourceSmoothOrbitIntegralGeometry910b.exit', 'SourceSmoothOrbitIntegralGeometry910b.log', 'SourceSmoothProjectiveOrbitSum.lean', 'SourceSmoothProjectiveOrbitSum897a.exit', 'SourceSmoothProjectiveOrbitSum897a.log', 'SourceSmoothProjectiveOrbitSum908a.exit', 'SourceSmoothProjectiveOrbitSum908a.log', 'SourceSmoothedWindingIntegralSplit.lean', 'SourceSmoothedWindingIntegralSplit945a.exit', 'SourceSmoothedWindingIntegralSplit945a.log', 'SourceSmoothedWindingIntegralSplit945b.exit', 'SourceSmoothedWindingIntegralSplit945b.log', 'SourceSmoothedWindingIntegralSplit945c.exit', 'SourceSmoothedWindingIntegralSplit945c.log', 'SourceUntwistPeterssonLimit.lean', 'SourceUntwistPeterssonLimit947a.exit', 'SourceUntwistPeterssonLimit947a.log', 'SourceUntwistPeterssonLimit947b.exit', 'SourceUntwistPeterssonLimit947b.log', 'SourceWeightTwoCosetPeriods.lean', 'SourceWeightTwoCosetPeriods939a.exit', 'SourceWeightTwoCosetPeriods939a.log', 'SourceWeightTwoCosetPeriods939b.exit', 'SourceWeightTwoCosetPeriods939b.log', 'SourceWeightTwoCosetPeriods939c.exit', 'SourceWeightTwoCosetPeriods939c.log', 'SourceWeightTwoPeriodUntwist.lean', 'SourceWeightTwoPrimitiveEdges.lean', 'SourceWeightTwoPrimitiveEdges938a.exit', 'SourceWeightTwoPrimitiveEdges938a.log', 'SourceWeightTwoPrimitiveEdges938b.exit', 'SourceWeightTwoPrimitiveEdges938b.log', 'SourceWeightTwoPrimitiveEdges938c.exit', 'SourceWeightTwoPrimitiveEdges938c.log', 'SourceWindingBoundaryIntegral.lean', 'SourceWindingBoundaryIntegral932a.exit', 'SourceWindingBoundaryIntegral932a.log', 'SourceWindingLogCuspBounds.lean', 'SourceWindingLogCuspBounds930a.exit', 'SourceWindingLogCuspBounds930a.log', 'SourceWindingLogCuspBounds930b.exit', 'SourceWindingLogCuspBounds930b.log', 'audit_divisor_winding_919.ps1', 'audit_modular_green_boundary_925.ps1', 'audit_original_divisor_winding_boundary_935.ps1', 'audit_original_petersson_reciprocity_950.ps1', 'audit_original_winding_integral_period_943.ps1', 'audit_original_winding_integral_period_943b.ps1', 'audit_smooth_divisor_909.ps1', 'audit_smooth_divisor_909b.ps1', 'audit_smooth_divisor_period_914.ps1', 'audit_smooth_divisor_period_914b.ps1', 'compile_smooth_divisor_pruned_908.ps1', 'consumers912.txt', 'consumers934.txt', 'consumers946.txt', 'docs934.py', 'docs946.py', 'foundation912-console.log', 'foundation934-console.log', 'foundation946-console.log', 'gamma-one-divisor-winding-comparison-route-918.json', 'gamma-one-local-model-construction-reuse-889\\S_ModularCurve_exists_invariant_localModel_dbarLogDeriv_eq_sum_finsum_translate_of_finiteIndex.lean.txt', 'gamma-one-reciprocity-reuse-848\\S_ModularCurve_exists_mem_periodLatticeOf_tendsto_windingPairing_smoothedFundamental.lean.txt', 'modular-green-cusp-route-924.json', 'modular-green-reuse-route-922.json', 'modular-side-pairing-reuse-route-920.json', 'modules912.json', 'modules934.json', 'modules946.json', 'original-divisor-winding-boundary-route-933.json', 'original-winding-integral-period-candidates-942.json', 'paper912-console.log', 'paper934-console.log', 'paper946-console.log', 'parabolic-integral-period-reuse-936\\S_ModularCurve_exists_mem_periodLatticeOf_eq_sum_intCast_mul_edgeIntegral_of_isParabolicHom.lean.txt', 'parabolic-integral-period-reuse-936\\manifest.json', 'parabolic-integral-period-route-937.json', 'prepare_compact_translate_integral_911.py', 'prepare_divisor_winding_audit_919.py', 'prepare_gamma_one_divisor_winding_918.py', 'prepare_gamma_one_smooth_divisor_comparison_906.py', 'prepare_gamma_one_smooth_divisor_comparison_906b.py', 'prepare_modular_side_pairing_action_920.py', 'prepare_smooth_comparison_cusps_916.py', 'prepare_smooth_comparison_quotient_915.py', 'prepare_smooth_divisor_audit_909.py', 'prepare_smooth_divisor_audit_909b.py', 'prepare_smooth_divisor_invariance_cusps_903.py', 'prepare_smooth_divisor_local_orders_902.py', 'prepare_smooth_divisor_local_product_901.py', 'prepare_smooth_divisor_log_derivative_904.py', 'prepare_smooth_divisor_orbit_data_898.py', 'prepare_smooth_divisor_period_912.py', 'prepare_smooth_divisor_period_audit_914.py', 'prepare_smooth_divisor_period_audit_914b.py', 'prepare_smooth_divisor_product_900.py', 'prepare_smooth_divisor_pruned_908.py', 'prepare_smooth_divisor_value_probe_907.py', 'prepare_smooth_invariant_comparison_905.py', 'prepare_smooth_modular_geometry_896.py', 'prepare_smooth_modular_log_derivative_899.py', 'prepare_smooth_orbit_integral_910.py', 'prepare_smooth_projective_orbit_sum_897.py', 'prepare_smooth_projective_representatives_895.py', 'rebuild_original_winding_integral_period_943b.ps1', 'record912.py', 'record934.py', 'record946.py', 'record_source_gamma_one_divisor_winding_919.py', 'record_source_gamma_one_smooth_divisor_909.py', 'record_source_gamma_one_smooth_divisor_909b.py', 'record_source_gamma_one_smooth_divisor_period_914.py', 'record_source_gamma_one_smooth_divisor_period_914b.py', 'record_source_modular_green_boundary_925.py', 'record_source_original_divisor_winding_boundary_935.py', 'record_source_original_petersson_reciprocity_950.py', 'record_source_original_winding_integral_period_943.py', 'record_source_original_winding_integral_period_943b.py', 'register912.py', 'register934.py', 'register946.py', 'registrations912.json', 'registrations934.json', 'registrations946.json', 'section912.txt', 'section934.txt', 'section946.txt', 'smooth-comparison-quotient-route-915.json', 'smooth-divisor-audit-kind-correction-909b.json', 'smooth-divisor-period-audit-namespace-correction-914b.json', 'smooth-divisor-period-route-912.json', 'smooth-local-model-route-892.json', 'smooth-orbit-integral-shorter-route-910.json', 'smooth-projective-orbit-route-898.json', 'source-complex-dipole-1-scratch-receipt.json', 'source-gamma-one-divisor-winding-1-audit-config.json', 'source-gamma-one-divisor-winding-1-reuse-review-20261027.json', 'source-gamma-one-divisor-winding-1-scratch-receipt.json', 'source-gamma-one-divisor-winding-audit-route-919.json', 'source-gamma-one-smooth-divisor-1b-audit-config.json', 'source-gamma-one-smooth-divisor-1b-reuse-review-20261027.json', 'source-gamma-one-smooth-divisor-1b-scratch-receipt.json', 'source-gamma-one-smooth-divisor-908-compile-config.json', 'source-gamma-one-smooth-divisor-audit-route-909.json', 'source-gamma-one-smooth-divisor-period-1b-audit-config.json', 'source-gamma-one-smooth-divisor-period-1b-reuse-review-20261027.json', 'source-gamma-one-smooth-divisor-period-1b-scratch-receipt.json', 'source-gamma-one-smooth-divisor-period-audit-route-914.json', 'source-gamma-one-smooth-divisor-probe-907.json', 'source-modular-green-boundary-1-audit-config.json', 'source-modular-green-boundary-1-reuse-review-20261027.json', 'source-modular-green-boundary-1-scratch-receipt.json', 'source-modular-green-boundary-audit-route-925.json', 'source-modular-green-boundary-probe-923.json', 'source-modular-parabolic-winding-log-1-scratch-receipt.json', 'source-original-divisor-winding-boundary-1-audit-config.json', 'source-original-divisor-winding-boundary-1-reuse-review-20261027.json', 'source-original-divisor-winding-boundary-1-scratch-receipt.json', 'source-original-divisor-winding-boundary-audit-route-935.json', 'source-original-divisor-winding-boundary-probe-934.json', 'source-original-petersson-reciprocity-1-audit-config.json', 'source-original-petersson-reciprocity-1-reuse-review-20261027.json', 'source-original-petersson-reciprocity-1-scratch-receipt.json', 'source-original-petersson-reciprocity-audit-route-950.json', 'source-original-winding-integral-period-1b-audit-config.json', 'source-original-winding-integral-period-1b-reuse-review-20261027.json', 'source-original-winding-integral-period-1b-scratch-receipt.json', 'source-original-winding-integral-period-audit-route-943.json', 'status912.txt', 'status934.txt', 'status946.txt']]
for folder in ['gamma-one-divisor-winding-failed-918a', 'gamma-one-winding-integral-period-failed-941a', 'modular-cusp-boundary-warning-924a', 'modular-green-measure-warning-927a', 'modular-green-pullback-warning-926a', 'modular-green-tile-warning-926b', 'modular-period-corners-failed-938c', 'modular-side-pairing-action-failed-920a', 'modular-smoothed-green-limit-failed-931a', 'modular-smoothed-green-paren-count-failed-931c', 'modular-smoothed-green-parentheses-failed-931b', 'parabolic-coset-potentials-doclint-943', 'parabolic-coset-potentials-failed-937a', 'parabolic-integral-period-reuse-936', 'smooth-compact-translate-failed-911a', 'smooth-comparison-dbar-failed-944a', 'smooth-divisor-incidental-lemmas-deferred-908', 'smooth-divisor-log-derivative-failed-904a', 'smooth-divisor-period-failed-912a', 'smooth-divisor-product-warning-900a', 'smooth-local-foundation-failed-898a', 'smooth-local-foundation-failed-899a', 'smooth-local-product-warning-901a', 'smooth-log-derivative-rewrite-failed-899b', 'smooth-modular-geometry-warning-896a', 'smooth-orbit-integral-change-variables-warning-910a', 'smooth-orbit-integral-change-variables-warning-910b', 'smooth-orbit-integral-geometry-warning-910a', 'smooth-projective-representatives-failed-895a', 'smoothed-winding-integral-split-beta-failed-945b', 'smoothed-winding-integral-split-failed-945a', 'untwist-petersson-limit-failed-947a', 'weight-two-coset-periods-import-failed-939a', 'weight-two-primitive-edges-import-failed-938a', 'weight-two-primitive-edges-warning-938b', 'winding-log-cusp-bounds-failed-930a']:
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
supplemental_review_path=r/archive_rel/'gamma-one-divisor-reciprocity-promotion-route-951.json'

audit = r / "Extension/Dubon2026/Audit.lean"
at = audit.read_text(encoding="utf-8")
for n in queries:
    assert not re.search(r"``" + re.escape(n) + r"(?=[,\s])", at)
tm, dm = "\n]\n\nprivate def publicConstructions", "\n]\n\nprivate def runAudit"
assert at.count(tm) == at.count(dm) == 1
at = at.replace(tm, "".join("\n  ,``" + n for n in theorems) + tm, 1)
at = at.replace(dm, "".join("\n  ," + chr(96)*2 + n for n in defs) + dm, 1)
research_path = r / "Tools/lean-reuse-audit-20261020.json"
reuse_path = r / "Tools/source-gamma-one-divisor-reciprocity.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt8721"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> arithmetic realization of original finite Gamma1 homogeneous-coefficient Hecke characters -> full/parabolic, transpose, diamond, Picard/H1 comparison -> actual differential and period geometry -> Abel-Jacobi principal-divisor converse -> analytic reciprocity.'
discharged = 'For the actual original degree-zero Gamma1 divisor, an invariant smooth comparison V is constructed with exact ramification-weighted local orders, central stabilizer multiplicities, nonzero cusp behavior and the original endpoint-period limit. The filled quotient supplies the actual logarithm and integral parabolic character. Curved Green, literal coset side pairing and the normalized smooth-domain limit identify its winding boundary sum. Integer coset potentials and the actual normalized primitive express that sum as an integer combination of actual periods; the signed-to-original bridge yields membership in the original Gamma1 integer lattice. Equal local orders split the dbar integral, using existing almost-everywhere nonvanishing. Two proved limits of the same integral yield the exact original divisor/period/Petersson reciprocity identity, including conjugation, minus sign and central normalization. No smooth comparison, winding period or limiting reciprocity identity is assumed as a certificate.'
boundary = 'The original meromorphic function, its exact prescribed divisor orders, nonzero cusp limits and unitary multiplier remain explicit upstream inputs. The representative divisor functional must be related to the original finite divisor class. Integral Petersson/real-period identification, multiplier triviality and the original principal-divisor converse remain. Global Picard/Hecke/diamond/H1, full/parabolic and transpose comparisons remain. Arithmetic realization of original finite homogeneous-coefficient Gamma1 characters, coefficient-field transport, Frobenius/inertia, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain. Finite characters, complex semisimplicity, Witt coefficients and universal deformation rings do not supply a characteristic-zero lift. 16/20; DUB-17--20 OPEN; all twenty gates unchanged.'
status = 'The fifty-five-module original-divisor reciprocity scope passes 341 public axiom queries, 533 exhaustive scratch theorem checks, sixteen linters per module and seven declaration-value audits with 413 required dependency checks, with zero diagnostics. Production aggregate, focused audits and sequential foundation/paper verification of the 8,776-module scope are pending.'
route = 'The October 27 search supplies pinned Apache-2.0 generic-subgroup proofs adapted to the actual original Gamma1 objects. Existing Mobius derivatives, native slash action, projective fibers, finite domain and null boundary replace bespoke geometry. Compact support gives eventual exact equality for the smooth-divisor integral. Existing normalized primitives, all-cusp limits, Green edge integrability, native rho and original S relations replace repeated analytic setup in the parabolic integer-period proof. Existing untwist nonvanishing avoids another exceptional-set construction. Direct equality of two limits gives reciprocity; the wedge identity remains proved and used upstream by the compact dipole. All substantial tasks are connected by audited declaration-VALUE dependencies to the actual source consumers. Root pins and proof limits are unchanged; promotion changes project import qualification only.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Actual original Gamma1 divisor and Petersson reciprocity (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 8,721-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
corrections = []
count = sum(z['exhaustiveTheorems'] for z in certs)
assert count == 533

docpaths = list(dict.fromkeys(r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]))
for f in docpaths:
    assert "\n\n" in f.read_text(encoding="utf-8")
readmes = [(r.parent / "README.md", "Current Project 83 status ("), (repo / "README.md", "Project 83 has an ")]
for f, prefix in readmes:
    assert sum(line.startswith(prefix) for line in f.read_text(encoding="utf-8").splitlines()) == 1
arch = r / "Dubon Architecture.md"
edge = '  GAMMAONESMOOTH8721["Exact original Gamma1 smooth partition and Petersson limit; wedge, parabolic logarithm and compact dipole proved. Invariant V, winding-period comparison, reciprocity, Abel-Jacobi, Picard/Hecke/H1, all-weight association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourceGammaOneDivisorReciprocityProductionAudit8776.lean',p/'source-gamma-one-divisor-reciprocity-8776-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production8776.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/gamma-one-smooth-comparison-20261027-894'
registered = {row['path'] for row in c['files']}
for priorFile in priorArchive.iterdir():
    rel = priorFile.relative_to(r).as_posix()
    if priorFile.is_file() and rel not in registered:
        c['files'].append({'path': rel, 'role': 'Tools'})

reportSource = p / 'Dubon Original Divisor Reciprocity Reuse Assessment 2026-10-27.md'
assert sha(reportSource) == '33224CC25F48519DD77D53DB1E3EE6A9A0EBE172B6377E7A7EC3A632A3910D32'
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
    "productionModules": 8776, "modules": newmods, "queries": queries,
    "theoremRegistrations": theorems, "constructionRegistrations": defs,
    "sourceHashes": {mapping[t.stem]: sha(t) for t, _ in pending}, "scratchCertificates": certs,
    "exactDependency": dependency, "assumptionsDischarged": discharged, "stillOpen": boundary,
    "status": status, "rootPinsChanged": False, "proofLimitsChanged": False,
    "promotionChanges": 'Only project scratch imports are qualified. All audited statements, proof bodies and comments remain identical. Original Gamma1 field, all nonzero levels, signed stabilizer normalization, original integer lattice and exact divisor orders are retained.',
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
arch.write_text(arch.read_text(encoding='utf-8').replace(edge,'  GAMMAONESMOOTH8721["Exact original Gamma1 smooth partition and Petersson limit; wedge, parabolic logarithm and compact dipole proved (DUB-17/18)"] --> GAMMAONEDIVISOR8776\n  GAMMAONEDIVISOR8776["Actual original divisor smooth comparison, filled quotient, integer winding period and divisor/Petersson reciprocity proved. Original meromorphic input, principal-divisor converse, Picard/Hecke/H1, all-weight association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'),encoding='utf-8')



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Actual original Gamma1 divisor and Petersson reciprocity - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-gamma-one-divisor-reciprocity.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub('  logInfo m!".*"\\n', '  logInfo m!"SOURCE GAMMA ONE DIVISOR RECIPROCITY AUDIT PASS: {count} theorems including private/generated declarations. Actual original divisor smooth comparison, filled quotient, integer winding period and divisor/Petersson reciprocity are proved. Original meromorphic input, principal-divisor converse and all-weight arithmetic remain; 16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourceGammaOneDivisorReciprocityProductionAudit8776.lean").write_text(out, encoding="utf-8")
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
    target = p / (source.stem + "Production8776.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
(p / "source-gamma-one-divisor-reciprocity-8776-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 8776, "increment": 55, "queries": 341,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
