from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 8776
assert d["appliedSourceGammaOneDivisorReciprocity"]["receipt8776"]["exit"] == 0
assert (p / "paper-verification-8776-console.exit").read_text().strip() == "0"
assert (r/'Tools/gamma-one-divisor-reciprocity-20261027-951/canonical-evidence-8776.json').exists()
key = "appliedSourceGammaOnePrincipalDivisor"
assert key not in d
digests = {'source-original-finite-divisor-reciprocity-1-scratch-receipt.json': 'B23F1B902FB2BE302835303B62448B78FA7D696A96E13EF012F3A15BA8584D8A', 'source-original-integral-period-duality-1b-scratch-receipt.json': '29A50919A8B2652B13105122A89E8616E3093FEB63AF3ABBF0009A48FB0715AA', 'source-original-general-multiplier-1-scratch-receipt.json': '5DEFEC3393F7ED949D5BB2DADD544417113222FE327F13A51DD33D9B9292C1B0', 'source-original-prescribed-residues-1b-scratch-receipt.json': '564A87FC0ECF527C42D886B1DD0DD5D73AD031A92FB14103A61AB40F6BA1EB3C', 'source-meromorphic-logarithmic-primitive-1-scratch-receipt.json': 'E318C329DA7622734C42033AE98E9A61F4B0B4BE4708B433452DD21C2F050F5D', 'source-gamma-one-analytic-residue-1-scratch-receipt.json': '043F53AB67A33BF9BE696CD5B64AD3EFC00474A9312778F53ADFE2DFAF6B636E', 'source-meromorphic-cusp-construction-1-scratch-receipt.json': '882433DFDA33D6C84F11D2EEB70044F92529A78A1267833BA388CC742A7200C7', 'source-gamma-one-principal-divisor-converse-1-scratch-receipt.json': 'D1999BCF1FBF9564C57398EDC6BD3242BD80BA4742C5A45425F221CE44E05F55'}

for name, digest in digests.items():
    assert sha(p / name) == digest
certs = [json.loads((p / name).read_text(encoding="utf-8")) for name in digests]
mods = [m for z in certs for m in z["modules"]]
queries = [q for z in certs for q in z["queries"]]
theorems = [q for z in certs for q in z["theoremRegistrations"]]
defs = [q for z in certs for q in z["constructionRegistrations"]]
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (45, 45, 242, 200, 42)
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
archive_rel='Tools/gamma-one-principal-divisor-20261027-1015'
evidence=[p/'gamma-one-principal-divisor-promotion-route-1015.json']
evidence += [p/n for n in ['SourceAnalyticResidueScalarProbe993.exit', 'SourceAnalyticResidueScalarProbe993.log', 'SourceAnalyticResidueScalarProbe993b.exit', 'SourceAnalyticResidueScalarProbe993b.log', 'SourceClosedPeterssonNondegenerate.lean', 'SourceClosedPeterssonNondegenerate965a.exit', 'SourceClosedPeterssonNondegenerate965a.log', 'SourceClosedPeterssonNondegenerate965b.exit', 'SourceClosedPeterssonNondegenerate965b.log', 'SourceClosedPeterssonNondegenerate965c.exit', 'SourceClosedPeterssonNondegenerate965c.log', 'SourceGammaOneAnalyticDifferentialResidue.lean', 'SourceGammaOneAnalyticDifferentialResidue990a.exit', 'SourceGammaOneAnalyticDifferentialResidue990a.log', 'SourceGammaOneAnalyticDifferentialResidue990b.exit', 'SourceGammaOneAnalyticDifferentialResidue990b.log', 'SourceGammaOneAnalyticDifferentialResidue990c.exit', 'SourceGammaOneAnalyticDifferentialResidue990c.log', 'SourceGammaOneAnalyticDifferentialResidue990d.exit', 'SourceGammaOneAnalyticDifferentialResidue990d.log', 'SourceGammaOneAnalyticDifferentialResidue990e.exit', 'SourceGammaOneAnalyticDifferentialResidue990e.log', 'SourceGammaOneAnalyticDifferentialResidue990f.exit', 'SourceGammaOneAnalyticDifferentialResidue990f.log', 'SourceGammaOneAnalyticDifferentialResidue990g.exit', 'SourceGammaOneAnalyticDifferentialResidue990g.log', 'SourceGammaOneAnalyticDivisorDifferential.lean', 'SourceGammaOneAnalyticDivisorDifferential981a.exit', 'SourceGammaOneAnalyticDivisorDifferential981a.log', 'SourceGammaOneAnalyticResidueAudit1.exit', 'SourceGammaOneAnalyticResidueAudit1.lean', 'SourceGammaOneAnalyticResidueAudit1.log', 'SourceGammaOneAnalyticResidueDependencyAudit1.exit', 'SourceGammaOneAnalyticResidueDependencyAudit1.lean', 'SourceGammaOneAnalyticResidueDependencyAudit1.log', 'SourceGammaOneAnalyticResidueScratchOwnership1003.exit', 'SourceGammaOneAnalyticResidueScratchOwnership1003.lean', 'SourceGammaOneAnalyticResidueScratchOwnership1003.log', 'SourceGammaOneAnalyticResidueValueProbe1002.exit', 'SourceGammaOneAnalyticResidueValueProbe1002.log', 'SourceGammaOneDifferentialResidues.lean', 'SourceGammaOneDifferentialResidues977a.exit', 'SourceGammaOneDifferentialResidues977a.log', 'SourceGammaOneFiniteDivisorReciprocity.lean', 'SourceGammaOneFiniteDivisorReciprocity954a.exit', 'SourceGammaOneFiniteDivisorReciprocity954a.log', 'SourceGammaOneFiniteDivisorReciprocityAssembled.lean', 'SourceGammaOneFiniteDivisorReciprocityAssembled969a.exit', 'SourceGammaOneFiniteDivisorReciprocityAssembled969a.log', 'SourceGammaOneGeneralMultiplierPrincipal-974a.exit', 'SourceGammaOneGeneralMultiplierPrincipal-974a.log', 'SourceGammaOneGeneralMultiplierPrincipal.lean', 'SourceGammaOneLocalRegularDifferentialOrder.lean', 'SourceGammaOneLocalRegularDifferentialOrder1008a.exit', 'SourceGammaOneLocalRegularDifferentialOrder1008a.log', 'SourceGammaOneLocalRegularDifferentialOrder1008b.exit', 'SourceGammaOneLocalRegularDifferentialOrder1008b.log', 'SourceGammaOneLocalRegularDifferentialOrder1008c.exit', 'SourceGammaOneLocalRegularDifferentialOrder1008c.log', 'SourceGammaOneLocalRegularDifferentialOrder1008d.exit', 'SourceGammaOneLocalRegularDifferentialOrder1008d.log', 'SourceGammaOneMultiplierUnitarization.lean', 'SourceGammaOneMultiplierUnitarization973a.exit', 'SourceGammaOneMultiplierUnitarization973a.log', 'SourceGammaOnePeterssonIntegralRealPeriods.lean', 'SourceGammaOnePeterssonIntegralRealPeriods968a.exit', 'SourceGammaOnePeterssonIntegralRealPeriods968a.log', 'SourceGammaOnePrescribedResidueCoefficient.lean', 'SourceGammaOnePrescribedResidueCoefficient1011a.exit', 'SourceGammaOnePrescribedResidueCoefficient1011a.log', 'SourceGammaOnePrescribedResidueCoefficient1011b.exit', 'SourceGammaOnePrescribedResidueCoefficient1011b.log', 'SourceGammaOnePrescribedResidueCoefficient1011c.exit', 'SourceGammaOnePrescribedResidueCoefficient1011c.log', 'SourceGammaOnePrescribedResidueCoefficient1011d.exit', 'SourceGammaOnePrescribedResidueCoefficient1011d.log', 'SourceGammaOnePrescribedResidues.lean', 'SourceGammaOnePrescribedResidues980a.exit', 'SourceGammaOnePrescribedResidues980a.log', 'SourceGammaOnePrincipalDivisorConverse.lean', 'SourceGammaOnePrincipalDivisorConverse1012a.exit', 'SourceGammaOnePrincipalDivisorConverse1012a.log', 'SourceGammaOnePrincipalDivisorConverseAudit1.exit', 'SourceGammaOnePrincipalDivisorConverseAudit1.lean', 'SourceGammaOnePrincipalDivisorConverseAudit1.log', 'SourceGammaOnePrincipalDivisorConverseDependencyAudit1.exit', 'SourceGammaOnePrincipalDivisorConverseDependencyAudit1.lean', 'SourceGammaOnePrincipalDivisorConverseDependencyAudit1.log', 'SourceGammaOnePrincipalDivisorConverseScratchOwnership1014.exit', 'SourceGammaOnePrincipalDivisorConverseScratchOwnership1014.lean', 'SourceGammaOnePrincipalDivisorConverseScratchOwnership1014.log', 'SourceGammaOnePrincipalDivisorConverseValueProbe1013.exit', 'SourceGammaOnePrincipalDivisorConverseValueProbe1013.log', 'SourceGammaOneRawDifferential.lean', 'SourceGammaOneRawDifferential1007a.exit', 'SourceGammaOneRawDifferential1007a.log', 'SourceGammaOneRawDifferential1007b.exit', 'SourceGammaOneRawDifferential1007b.log', 'SourceGammaOneRawDifferentialDecay.lean', 'SourceGammaOneRawDifferentialDecay1010a.exit', 'SourceGammaOneRawDifferentialDecay1010a.log', 'SourceGammaOneRealizationDerivation.lean', 'SourceGammaOneRealizationDerivation989a.exit', 'SourceGammaOneRealizationDerivation989a.log', 'SourceGammaOneRealizationDerivation989b.exit', 'SourceGammaOneRealizationDerivation989b.log', 'SourceGammaOneRepresentativePeriodCorrection.lean', 'SourceGammaOneRepresentativePeriodCorrection953a.exit', 'SourceGammaOneRepresentativePeriodCorrection953a.log', 'SourceGammaOneRepresentativePeriodCorrection953b.exit', 'SourceGammaOneRepresentativePeriodCorrection953b.log', 'SourceGammaOneRepresentativePeriods.lean', 'SourceGammaOneRepresentativePeriods952a.exit', 'SourceGammaOneRepresentativePeriods952a.log', 'SourceGammaOneRepresentativePeriods952b.exit', 'SourceGammaOneRepresentativePeriods952b.log', 'SourceGammaOneSignedRealPeriods.lean', 'SourceGammaOneSignedRealPeriods967a.exit', 'SourceGammaOneSignedRealPeriods967a.log', 'SourceGammaOneSimplePoleBounds.lean', 'SourceGammaOneSimplePoleBounds978a.exit', 'SourceGammaOneSimplePoleBounds978a.log', 'SourceGammaOneTwoPoleDifferential.lean', 'SourceGammaOneTwoPoleDifferential976a.exit', 'SourceGammaOneTwoPoleDifferential976a.log', 'SourceGammaOneTwoPoleDifferential976b.exit', 'SourceGammaOneTwoPoleDifferential976b.log', 'SourceGammaOneTwoPoleDifferential976c.exit', 'SourceGammaOneTwoPoleDifferential976c.log', 'SourceGammaOneTwoPoleDifferential976d.exit', 'SourceGammaOneTwoPoleDifferential976d.log', 'SourceGammaOneTwoPoleResidues.lean', 'SourceGammaOneTwoPoleResidues979a.exit', 'SourceGammaOneTwoPoleResidues979a.log', 'SourceGammaOneUnitaryDivisorPrincipal.lean', 'SourceGammaOneUnitaryDivisorPrincipal970a.exit', 'SourceGammaOneUnitaryDivisorPrincipal970a.log', 'SourceIntegralCosetCocycle.lean', 'SourceIntegralCosetCocycle957a.exit', 'SourceIntegralCosetCocycle957a.log', 'SourceIntegralCosetCocycle957b.exit', 'SourceIntegralCosetCocycle957b.log', 'SourceIntegralCosetParabolic.lean', 'SourceIntegralCosetParabolic958a.exit', 'SourceIntegralCosetParabolic958a.log', 'SourceIntegralCosetParabolic958b.exit', 'SourceIntegralCosetParabolic958b.log', 'SourceIntegralCosetWord.lean', 'SourceIntegralCosetWord959a.exit', 'SourceIntegralCosetWord959a.log', 'SourceIntegralCosetWord959b.exit', 'SourceIntegralCosetWord959b.log', 'SourceIntegralPeriodCuspLimits.lean', 'SourceIntegralPeriodCuspLimits960a.exit', 'SourceIntegralPeriodCuspLimits960a.log', 'SourceIntegralPeriodCuspLimits960b.exit', 'SourceIntegralPeriodCuspLimits960b.log', 'SourceIntegralPeriodGeneratorDual.lean', 'SourceIntegralPeriodGeneratorDual961a.exit', 'SourceIntegralPeriodGeneratorDual961a.log', 'SourceIntegralPeriodGeneratorDual961b.exit', 'SourceIntegralPeriodGeneratorDual961b.log', 'SourceIntegralPeriodLatticeDual.lean', 'SourceIntegralPeriodLatticeDual963a.exit', 'SourceIntegralPeriodLatticeDual963a.log', 'SourceIntegralPeriodLatticeDual963b.exit', 'SourceIntegralPeriodLatticeDual963b.log', 'SourceMeromorphicCuspAnalyticData.lean', 'SourceMeromorphicCuspAnalyticData997a.exit', 'SourceMeromorphicCuspAnalyticData997a.log', 'SourceMeromorphicCuspConstructionAudit1.exit', 'SourceMeromorphicCuspConstructionAudit1.lean', 'SourceMeromorphicCuspConstructionAudit1.log', 'SourceMeromorphicCuspConstructionDependencyAudit1.exit', 'SourceMeromorphicCuspConstructionDependencyAudit1.lean', 'SourceMeromorphicCuspConstructionDependencyAudit1.log', 'SourceMeromorphicCuspConstructionScratchOwnership1005.exit', 'SourceMeromorphicCuspConstructionScratchOwnership1005.lean', 'SourceMeromorphicCuspConstructionScratchOwnership1005.log', 'SourceMeromorphicCuspConstructionValueProbe1004.exit', 'SourceMeromorphicCuspConstructionValueProbe1004.log', 'SourceMeromorphicCuspExponentialDecay.lean', 'SourceMeromorphicCuspExponentialDecay1009a.exit', 'SourceMeromorphicCuspExponentialDecay1009a.log', 'SourceMeromorphicCuspExponentialDecay1009b.exit', 'SourceMeromorphicCuspExponentialDecay1009b.log', 'SourceMeromorphicCuspPrimitive.lean', 'SourceMeromorphicCuspPrimitive998a.exit', 'SourceMeromorphicCuspPrimitive998a.log', 'SourceMeromorphicCuspPrimitive998b.exit', 'SourceMeromorphicCuspPrimitive998b.log', 'SourceMeromorphicCuspPrimitiveDecay.lean', 'SourceMeromorphicCuspPrimitiveDecay999a.exit', 'SourceMeromorphicCuspPrimitiveDecay999a.log', 'SourceMeromorphicDifferentialRegularization.lean', 'SourceMeromorphicDifferentialRegularization1006a.exit', 'SourceMeromorphicDifferentialRegularization1006a.log', 'SourceMeromorphicDiscPrimitive.lean', 'SourceMeromorphicDiscPrimitive987a.exit', 'SourceMeromorphicDiscPrimitive987a.log', 'SourceMeromorphicFinitePolarProduct.lean', 'SourceMeromorphicFinitePolarProduct985a.exit', 'SourceMeromorphicFinitePolarProduct985a.log', 'SourceMeromorphicLogarithmicPrimitiveAudit1.exit', 'SourceMeromorphicLogarithmicPrimitiveAudit1.lean', 'SourceMeromorphicLogarithmicPrimitiveAudit1.log', 'SourceMeromorphicLogarithmicPrimitiveDependencyAudit1.exit', 'SourceMeromorphicLogarithmicPrimitiveDependencyAudit1.lean', 'SourceMeromorphicLogarithmicPrimitiveDependencyAudit1.log', 'SourceMeromorphicLogarithmicPrimitiveScratchOwnership992.exit', 'SourceMeromorphicLogarithmicPrimitiveScratchOwnership992.lean', 'SourceMeromorphicLogarithmicPrimitiveScratchOwnership992.log', 'SourceMeromorphicLogarithmicPrimitiveValueProbe991.exit', 'SourceMeromorphicLogarithmicPrimitiveValueProbe991.log', 'SourceMeromorphicPrimitiveCusps.lean', 'SourceMeromorphicPrimitiveCusps1000a.exit', 'SourceMeromorphicPrimitiveCusps1000a.log', 'SourceMeromorphicPrimitiveCusps1000b.exit', 'SourceMeromorphicPrimitiveCusps1000b.log', 'SourceMeromorphicPrimitiveGroupAction.lean', 'SourceMeromorphicPrimitiveGroupAction995a.exit', 'SourceMeromorphicPrimitiveGroupAction995a.log', 'SourceMeromorphicPrimitiveGroupAction995b.exit', 'SourceMeromorphicPrimitiveGroupAction995b.log', 'SourceMeromorphicPrimitiveMultiplier.lean', 'SourceMeromorphicPrimitiveMultiplier996a.exit', 'SourceMeromorphicPrimitiveMultiplier996a.log', 'SourceMeromorphicPrimitiveMultiplier996b.exit', 'SourceMeromorphicPrimitiveMultiplier996b.log', 'SourceMeromorphicPrimitiveSpecification.lean', 'SourceMeromorphicPrimitiveSpecification994a.exit', 'SourceMeromorphicPrimitiveSpecification994a.log', 'SourceOriginalFiniteDivisorReciprocityAudit1.exit', 'SourceOriginalFiniteDivisorReciprocityAudit1.lean', 'SourceOriginalFiniteDivisorReciprocityAudit1.log', 'SourceOriginalFiniteDivisorReciprocityDependencyAudit1.exit', 'SourceOriginalFiniteDivisorReciprocityDependencyAudit1.lean', 'SourceOriginalFiniteDivisorReciprocityDependencyAudit1.log', 'SourceOriginalFiniteDivisorReciprocityScratchOwnership956.exit', 'SourceOriginalFiniteDivisorReciprocityScratchOwnership956.lean', 'SourceOriginalFiniteDivisorReciprocityScratchOwnership956.log', 'SourceOriginalFiniteDivisorReciprocityValueProbe955.exit', 'SourceOriginalFiniteDivisorReciprocityValueProbe955.lean', 'SourceOriginalFiniteDivisorReciprocityValueProbe955.log', 'SourceOriginalGeneralMultiplierAudit1.exit', 'SourceOriginalGeneralMultiplierAudit1.lean', 'SourceOriginalGeneralMultiplierAudit1.log', 'SourceOriginalGeneralMultiplierDependencyAudit1.exit', 'SourceOriginalGeneralMultiplierDependencyAudit1.lean', 'SourceOriginalGeneralMultiplierDependencyAudit1.log', 'SourceOriginalGeneralMultiplierScratchOwnership975.exit', 'SourceOriginalGeneralMultiplierScratchOwnership975.lean', 'SourceOriginalGeneralMultiplierScratchOwnership975.log', 'SourceOriginalIntegralPeriodDualityAudit1b.exit', 'SourceOriginalIntegralPeriodDualityAudit1b.lean', 'SourceOriginalIntegralPeriodDualityAudit1b.log', 'SourceOriginalIntegralPeriodDualityDependencyAudit1b.exit', 'SourceOriginalIntegralPeriodDualityDependencyAudit1b.lean', 'SourceOriginalIntegralPeriodDualityDependencyAudit1b.log', 'SourceOriginalIntegralPeriodDualityScratchOwnership972.exit', 'SourceOriginalIntegralPeriodDualityScratchOwnership972.lean', 'SourceOriginalIntegralPeriodDualityScratchOwnership972.log', 'SourceOriginalIntegralPeriodDualityValueProbe971.exit', 'SourceOriginalIntegralPeriodDualityValueProbe971.lean', 'SourceOriginalIntegralPeriodDualityValueProbe971.log', 'SourceOriginalPrescribedResiduesAudit1b.exit', 'SourceOriginalPrescribedResiduesAudit1b.lean', 'SourceOriginalPrescribedResiduesAudit1b.log', 'SourceOriginalPrescribedResiduesDependencyAudit1b.exit', 'SourceOriginalPrescribedResiduesDependencyAudit1b.lean', 'SourceOriginalPrescribedResiduesDependencyAudit1b.log', 'SourceOriginalPrescribedResiduesScratchOwnership983.exit', 'SourceOriginalPrescribedResiduesScratchOwnership983.lean', 'SourceOriginalPrescribedResiduesScratchOwnership983.log', 'SourceOriginalPrescribedResiduesValueProbe982.exit', 'SourceOriginalPrescribedResiduesValueProbe982.log', 'SourceRealPeriodPeterssonPairing.lean', 'SourceRealPeriodPeterssonPairing964a.exit', 'SourceRealPeriodPeterssonPairing964a.log', 'SourceRealPeriodPeterssonPairing964b.exit', 'SourceRealPeriodPeterssonPairing964b.log', 'SourceRealPeriodPeterssonPairing964c.exit', 'SourceRealPeriodPeterssonPairing964c.log', 'SourceRealPeriodPeterssonPairing964d.exit', 'SourceRealPeriodPeterssonPairing964d.log', 'SourceRealPrimitiveGreenData.lean', 'SourceRealPrimitiveGreenData962a.exit', 'SourceRealPrimitiveGreenData962a.log', 'SourceRealPrimitiveGreenData962b.exit', 'SourceRealPrimitiveGreenData962b.log', 'SourceSignedPeriodLatticeLift.lean', 'SourceSignedPeriodLatticeLift966a.exit', 'SourceSignedPeriodLatticeLift966a.log', 'SourceUpperHalfPlaneDiscExhaustion.lean', 'SourceUpperHalfPlaneDiscExhaustion986a.exit', 'SourceUpperHalfPlaneDiscExhaustion986a.log', 'SourceUpperHalfPlaneMeromorphicPrimitive.lean', 'SourceUpperHalfPlaneMeromorphicPrimitive988a.exit', 'SourceUpperHalfPlaneMeromorphicPrimitive988a.log', 'SourceUpperHalfPlaneMeromorphicPrimitive988b.exit', 'SourceUpperHalfPlaneMeromorphicPrimitive988b.log', 'SourceUpperHalfPlaneMeromorphicPrimitive988c.exit', 'SourceUpperHalfPlaneMeromorphicPrimitive988c.log', 'SourceUpperHalfPlaneMeromorphicPrimitive988d.exit', 'SourceUpperHalfPlaneMeromorphicPrimitive988d.log', 'SourceUpperHalfPlaneResidueData.lean', 'SourceUpperHalfPlaneResidueData984a.exit', 'SourceUpperHalfPlaneResidueData984a.log', 'anthropic-flt-residual-closure-20261020\\P2M\\Sol\\S_ModularCurve_ComplexPlaceDictionary_exists_norm_multiplier_eq_one_and_abelJacobi_add_petersson_mem_periodLattice.lean.txt', 'anthropic-flt-residual-closure-20261020\\P2M\\Sol\\S_ModularCurve_ComplexPlaceDictionary_exists_realize_mul_deriv_realize_eq_div_add.lean.txt', 'anthropic-flt-residual-closure-20261020\\P2M\\Sol\\S_ModularCurve_ComplexPlaceDictionary_exists_slashInvariant_residue_eq_of_degree_eq_zero.lean.txt', 'anthropic-flt-residual-closure-20261020\\P2M\\Sol\\S_ModularCurve_exists_meromorphic_logDeriv_eq_of_int_residue.lean.txt', 'anthropic-flt-residual-closure-20261020\\P2M\\Sol\\S_ModularCurve_exists_meromorphic_smul_eq_mul_of_slashInvariant_residue.lean.txt', 'audit_gamma_one_analytic_residue_1003.ps1', 'audit_gamma_one_principal_divisor_converse_1014.ps1', 'audit_meromorphic_cusp_construction_1005.ps1', 'audit_meromorphic_logarithmic_primitive_992.ps1', 'audit_original_finite_divisor_reciprocity_956.ps1', 'audit_original_general_multiplier_975.ps1', 'audit_original_integral_period_duality_972.ps1', 'audit_original_prescribed_residues_983.ps1', 'consumers963.txt', 'consumers979.txt', 'consumers987.txt', 'consumers996.txt', 'docs963.py', 'docs979.py', 'docs987.py', 'docs996.py', 'finite-divisor-reciprocity-assembled-body-969.json', 'foundation963-console.log', 'foundation979-console.log', 'foundation987-console.log', 'foundation996-console.log', 'modules963.json', 'modules979.json', 'modules987.json', 'modules996.json', 'paper963-console.log', 'paper979-console.log', 'paper987-console.log', 'paper996-console.log', 'prepare_meromorphic_primitive_audit_992.py', 'record963.py', 'record979.py', 'record987.py', 'record996.py', 'record_source_gamma_one_analytic_residue_1003.py', 'record_source_gamma_one_principal_divisor_converse_1014.py', 'record_source_meromorphic_cusp_construction_1005.py', 'record_source_meromorphic_logarithmic_primitive_992.py', 'record_source_original_finite_divisor_reciprocity_956.py', 'record_source_original_general_multiplier_975.py', 'record_source_original_integral_period_duality_972.py', 'record_source_original_prescribed_residues_983.py', 'register963.py', 'register979.py', 'register987.py', 'register996.py', 'registrations963.json', 'registrations979.json', 'registrations987.json', 'registrations996.json', 'section963.txt', 'section979.txt', 'section987.txt', 'section996.txt', 'source-gamma-one-actual-differential-input-route-1007.json', 'source-gamma-one-analytic-residue-1-audit-config.json', 'source-gamma-one-analytic-residue-1-reuse-review-20261027.json', 'source-gamma-one-analytic-residue-1-scratch-receipt.json', 'source-gamma-one-analytic-residue-audit-route-1003.json', 'source-gamma-one-analytic-residue-route-990.json', 'source-gamma-one-prescribed-residues-route-976.json', 'source-gamma-one-principal-divisor-converse-1-audit-config.json', 'source-gamma-one-principal-divisor-converse-1-reuse-review-20261027.json', 'source-gamma-one-principal-divisor-converse-1-scratch-receipt.json', 'source-gamma-one-principal-divisor-converse-audit-route-1014.json', 'source-gamma-one-unitarization-route-973.json', 'source-integral-period-duality-route-957.json', 'source-meromorphic-cusp-construction-1-audit-config.json', 'source-meromorphic-cusp-construction-1-reuse-review-20261027.json', 'source-meromorphic-cusp-construction-1-scratch-receipt.json', 'source-meromorphic-cusp-construction-audit-route-1005.json', 'source-meromorphic-cusp-construction-route-997.json', 'source-meromorphic-differential-regularization-route-1006.json', 'source-meromorphic-logarithmic-primitive-1-audit-config.json', 'source-meromorphic-logarithmic-primitive-1-reuse-review-20261027.json', 'source-meromorphic-logarithmic-primitive-1-scratch-receipt.json', 'source-meromorphic-logarithmic-primitive-audit-route-992.json', 'source-meromorphic-multiplier-route-994.json', 'source-original-finite-divisor-reciprocity-1-audit-config.json', 'source-original-finite-divisor-reciprocity-1-reuse-review-20261027.json', 'source-original-finite-divisor-reciprocity-1-scratch-receipt.json', 'source-original-finite-divisor-reciprocity-audit-route-956.json', 'source-original-general-multiplier-1-audit-config.json', 'source-original-general-multiplier-1-reuse-review-20261027.json', 'source-original-general-multiplier-1-scratch-receipt.json', 'source-original-general-multiplier-audit-route-975.json', 'source-original-integral-period-duality-1b-audit-config.json', 'source-original-integral-period-duality-1b-reuse-review-20261027.json', 'source-original-integral-period-duality-1b-scratch-receipt.json', 'source-original-integral-period-duality-audit-route-972.json', 'source-original-petersson-reciprocity-1-scratch-receipt.json', 'source-original-prescribed-residues-1b-audit-config.json', 'source-original-prescribed-residues-1b-reuse-review-20261027.json', 'source-original-prescribed-residues-1b-scratch-receipt.json', 'source-original-prescribed-residues-audit-route-983.json', 'source-real-primitive-green-route-962.json', 'source-upper-half-plane-meromorphic-primitive-route-984.json', 'status963.txt', 'status979.txt', 'status987.txt', 'status996.txt']]
for folder in ['closed-petersson-nondegenerate-failed-965a', 'closed-petersson-nondegenerate-signed-rewrite-failed-965b', 'gamma-one-analytic-residue-action-inference-failed-990d', 'gamma-one-analytic-residue-explicit-instance-failed-990f', 'gamma-one-analytic-residue-inference-failed-990a', 'gamma-one-analytic-residue-inference-failed-990b', 'gamma-one-analytic-residue-module-inference-failed-990e', 'gamma-one-analytic-residue-scalar-inference-failed-990c', 'gamma-one-local-regular-order-algebra-mismatch-1008c', 'gamma-one-local-regular-order-inference-1008b', 'gamma-one-raw-differential-closed-goal-1007a', 'gamma-one-realization-derivation-context-failed-989a', 'gamma-one-representative-periods-failed-952a', 'gamma-one-residue-coefficient-eta-token-1011a', 'gamma-one-residue-coefficient-local-coordinate-1011c', 'gamma-one-residue-coefficient-nontrivial-1011b', 'gamma-one-two-pole-canonical-rewrite-failed-976b', 'gamma-one-two-pole-context-failed-976a', 'gamma-one-two-pole-instance-failed-976c', 'integral-coset-cocycle-failed-957a', 'integral-coset-parabolic-failed-958a', 'integral-coset-word-encoding-failed-959a', 'integral-period-cusp-limits-failed-960a', 'integral-period-generator-dual-failed-961a', 'integral-period-lattice-dual-failed-963a', 'meromorphic-action-unused-tactic-995a', 'meromorphic-cusp-consumer-preassembly-1000a', 'meromorphic-cusp-exponential-q-rewrite-1009a', 'meromorphic-cusp-primitive-unused-scope-998a', 'meromorphic-multiplier-convert-failed-996a', 'real-period-petersson-pairing-defeq-failed-964c', 'real-period-petersson-pairing-import-failed-964a', 'real-period-petersson-pairing-transition-failed-964b', 'real-primitive-green-data-failed-962a', 'representative-period-correction-failed-953a', 'upper-half-plane-primitive-convert-failed-988a', 'upper-half-plane-primitive-convert-failed-988b', 'upper-half-plane-primitive-sequence-warning-988c']:
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
supplemental_review_path=r/archive_rel/'gamma-one-principal-divisor-promotion-route-1015.json'

audit = r / "Extension/Dubon2026/Audit.lean"
at = audit.read_text(encoding="utf-8")
for n in queries:
    assert not re.search(r"``" + re.escape(n) + r"(?=[,\s])", at)
tm, dm = "\n]\n\nprivate def publicConstructions", "\n]\n\nprivate def runAudit"
assert at.count(tm) == at.count(dm) == 1
at = at.replace(tm, "".join("\n  ,``" + n for n in theorems) + tm, 1)
at = at.replace(dm, "".join("\n  ," + chr(96)*2 + n for n in defs) + dm, 1)
research_path = r / "Tools/lean-reuse-audit-20261020.json"
reuse_path = r / "Tools/source-gamma-one-principal-divisor.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt8776"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> arithmetic realization of original finite Gamma1 homogeneous-coefficient Hecke characters -> full/parabolic, transpose, diamond, Picard/H1 comparison -> actual differential and period geometry -> Abel-Jacobi principal-divisor converse.'
discharged = 'Every finite degree-zero analytic divisor on the actual original Gamma1 integral-ratio field with original integral period class is now proved literally principal. Representative correction identifies its original finite period functional; integer cocycles and the actual Petersson pairing prove the required lattice duality. Unitarization removes the unit-modulus assumption. Native Riemann-Roch constructs the actual prescribed algebraic differential, including regularity at all j-poles. Its analytic realization gives the exact ramification-weighted integer residues, slash invariance and exponential cusp decay. Point regularization, meromorphic primitive construction and multiplier gluing give an actual meromorphic function with exact orders and nonzero limits at every translated cusp. Thus no meromorphic function, multiplier, cusp limit, exact-order certificate or analytic residue coefficient remains assumed in the finite-divisor converse.'
boundary = 'The forward principal-divisor period implication and full original Gamma1 Picard/Hecke/diamond/H1, full/parabolic and transpose comparisons remain. Arithmetic realization of original finite homogeneous-coefficient Gamma1 characters, coefficient-field transport, Frobenius/inertia, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain. Finite characters, complex semisimplicity, Witt coefficients and universal deformation rings do not supply a characteristic-zero lift. 16/20; DUB-17--20 OPEN; all twenty gates unchanged.'
status = 'The forty-five-module actual Gamma1 finite-divisor converse scope passes 242 public axiom queries, 376 exhaustive scratch theorem checks, sixteen linters per module and eight declaration-value audits with 488 required dependency checks, with zero diagnostics. Production aggregate, focused audits and sequential foundation/paper verification of the 8,821-module scope are pending.'
route = 'The October 27 pinned external search is now used through selected locally kernel-checked proofs. Native actual Gamma1 Riemann-Roch, residue surjectivity, realization germs, uniformizer logarithmic expansion, original period surjectivity and Petersson positivity discharge the geometric inputs. Native normalized wedge primitives avoid a second disk exhaustion; native q-parameter normal forms give decay from positive cusp order directly. The final converse has 240 declarations in its proof-VALUE closure, covering every public declaration of this 45-module scope except two separately axiom-checked definitional accessors optimized away by elaboration. No unrelated generalizations, external closure, root pin changes or proof-limit changes are introduced.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Actual original Gamma1 finite-divisor converse (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 8,776-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
corrections = []
count = sum(z['exhaustiveTheorems'] for z in certs)
assert count == 376

docpaths = list(dict.fromkeys(r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]))
for f in docpaths:
    assert "\n\n" in f.read_text(encoding="utf-8")
readmes = [(r.parent / "README.md", "Current Project 83 status ("), (repo / "README.md", "Project 83 has an ")]
for f, prefix in readmes:
    assert sum(line.startswith(prefix) for line in f.read_text(encoding="utf-8").splitlines()) == 1
arch = r / "Dubon Architecture.md"
edge = '  GAMMAONEDIVISOR8776["Actual original divisor smooth comparison, filled quotient, integer winding period and divisor/Petersson reciprocity proved. Original meromorphic input, principal-divisor converse, Picard/Hecke/H1, all-weight association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourceGammaOnePrincipalDivisorProductionAudit8821.lean',p/'source-gamma-one-principal-divisor-8821-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production8821.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/gamma-one-divisor-reciprocity-20261027-951'
registered = {row['path'] for row in c['files']}
for priorFile in priorArchive.iterdir():
    rel = priorFile.relative_to(r).as_posix()
    if priorFile.is_file() and rel not in registered:
        c['files'].append({'path': rel, 'role': 'Tools'})

reportSource = p / 'Dubon Principal Divisor Reuse Assessment 2026-10-27.md'
assert sha(reportSource) == '884BE165CEA584EB5921D7E345541E19B5304CE94D668C9E2BB86C99560E3F93'
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
    "productionModules": 8821, "modules": newmods, "queries": queries,
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
arch.write_text(arch.read_text(encoding='utf-8').replace(edge,'  GAMMAONEDIVISOR8776["Actual original divisor/Petersson reciprocity proved (DUB-17/18)"] --> GAMMAONEPRINCIPAL8821\n  GAMMAONEPRINCIPAL8821["Original integral period class implies literal principalness for every finite degree-zero Gamma1 analytic divisor. Actual residue differential, meromorphic function, multiplier and cusp inputs constructed. Forward implication, full Picard/Hecke/H1, all-weight association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'),encoding='utf-8')



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Actual original Gamma1 finite-divisor converse - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-gamma-one-principal-divisor.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub('  logInfo m!".*"\\n', '  logInfo m!"SOURCE GAMMA ONE PRINCIPAL DIVISOR AUDIT PASS: {count} theorems including private/generated declarations. The original integral-period condition implies literal principalness for every finite degree-zero Gamma1 analytic divisor. The meromorphic function and its analytic inputs are constructed. Forward implication, full Picard/H1 and all-weight arithmetic remain; 16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourceGammaOnePrincipalDivisorProductionAudit8821.lean").write_text(out, encoding="utf-8")
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
    target = p / (source.stem + "Production8821.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
(p / "source-gamma-one-principal-divisor-8821-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 8821, "increment": 45, "queries": 242,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
