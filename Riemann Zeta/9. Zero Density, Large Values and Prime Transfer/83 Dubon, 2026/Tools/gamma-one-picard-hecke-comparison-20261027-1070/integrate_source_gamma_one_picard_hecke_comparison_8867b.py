from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 8821
assert d["appliedSourceGammaOnePrincipalDivisor"]["receipt8821"]["exit"] == 0
assert (p / "paper-verification-8821b-console.exit").read_text().strip() == "0"
assert (r/'Tools/gamma-one-principal-divisor-20261027-1015/canonical-evidence-8821.json').exists()
key = "appliedSourceGammaOnePicardHeckeComparison"
assert key not in d
digests = {'source-gamma-one-analytic-abel-kernel-1-scratch-receipt.json': 'E0153A1CEABD4E221773F9D0745C74E5063CD9CC62D4160EDC1B029D88C2C2F9', 'source-gamma-one-picard-period-equivalence-1d-scratch-receipt.json': 'A0D6E1AFA9202CB59E957AA2A5447821798C7D441BAA6CD17750897D2180E915', 'source-gamma-one-hecke-analytic-maps-1-scratch-receipt.json': '62DF38F332F2A0C072C6A972B2B62990A147E57D746E18EF332D59FC11CAFB0B', 'source-gamma-one-hecke-primitive-trace-1-scratch-receipt.json': 'B174BF1883DD620FB8EE4CA08B91B0AAF863B5E34D8469F1CF3144871B649824', 'source-gamma-one-holomorphic-h1-hecke-1-scratch-receipt.json': '7B98EE4DC297818A33481D3A557EB45EA46A27EC5E2847D711B4EFD189944DE3', 'source-gamma-one-period-lattice-hecke-1b-scratch-receipt.json': 'BC598C78165F495868E275C576A2BA605A05DFC5B18569B209F1FA2AFB177A23', 'source-gamma-one-hecke-geometric-fibers-1b-scratch-receipt.json': '4A1288D3DD927497801D2D46F720D5A88A91242FC63FF19124EB580B607ED774', 'source-gamma-one-picard-period-hecke-1-scratch-receipt.json': '8D629BB414A820E1B6952A0DA3AF5F0C3BDD31C977CDBB48E7E137CE553836F3'}

for name, digest in digests.items():
    assert sha(p / name) == digest
certs = [json.loads((p / name).read_text(encoding="utf-8")) for name in digests]
mods = [m for z in certs for m in z["modules"]]
queries = [q for z in certs for q in z["queries"]]
theorems = [q for z in certs for q in z["theoremRegistrations"]]
defs = [q for z in certs for q in z["constructionRegistrations"]]
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (46, 46, 128, 100, 28)
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
archive_rel='Tools/gamma-one-picard-hecke-comparison-20261027-1070'
evidence=[p/'gamma-one-picard-hecke-comparison-promotion-route-1070.json']
evidence += [p/n for n in ['SourceGammaOneAnalyticAbelKernel.lean', 'SourceGammaOneAnalyticAbelKernel1018a.exit', 'SourceGammaOneAnalyticAbelKernel1018a.log', 'SourceGammaOneAnalyticAbelKernelAudit1.exit', 'SourceGammaOneAnalyticAbelKernelAudit1.lean', 'SourceGammaOneAnalyticAbelKernelAudit1.log', 'SourceGammaOneAnalyticAbelKernelDependencyAudit1.exit', 'SourceGammaOneAnalyticAbelKernelDependencyAudit1.lean', 'SourceGammaOneAnalyticAbelKernelDependencyAudit1.log', 'SourceGammaOneAnalyticAbelKernelScratchOwnership1019.exit', 'SourceGammaOneAnalyticAbelKernelScratchOwnership1019.lean', 'SourceGammaOneAnalyticAbelKernelScratchOwnership1019.log', 'SourceGammaOneAnalyticHeckeDivisors.lean', 'SourceGammaOneAnalyticHeckeDivisors1066a.exit', 'SourceGammaOneAnalyticHeckeDivisors1066a.log', 'SourceGammaOneAnalyticPicardPresentation.lean', 'SourceGammaOneAnalyticPicardPresentation1025a.exit', 'SourceGammaOneAnalyticPicardPresentation1025a.log', 'SourceGammaOneAnalyticPicardPresentation1025b.exit', 'SourceGammaOneAnalyticPicardPresentation1025b.log', 'SourceGammaOneAnalyticPicardPresentation1025c.exit', 'SourceGammaOneAnalyticPicardPresentation1025c.log', 'SourceGammaOneAnalyticPicardPresentation1025d.exit', 'SourceGammaOneAnalyticPicardPresentation1025d.log', 'SourceGammaOneAnalyticPicardPresentation1029c.exit', 'SourceGammaOneAnalyticPicardPresentation1029c.log', 'SourceGammaOneCentralStabilizerCard.lean', 'SourceGammaOneCentralStabilizerCard1061a.exit', 'SourceGammaOneCentralStabilizerCard1061a.log', 'SourceGammaOneCentralStabilizerCard1061b.exit', 'SourceGammaOneCentralStabilizerCard1061b.log', 'SourceGammaOneCuspHeckeLinear.lean', 'SourceGammaOneCuspHeckeLinear1048a.exit', 'SourceGammaOneCuspHeckeLinear1048a.log', 'SourceGammaOneCuspHeckeLinear1048b.exit', 'SourceGammaOneCuspHeckeLinear1048b.log', 'SourceGammaOneCuspHeckeTrace.lean', 'SourceGammaOneCuspHeckeTrace1039a.exit', 'SourceGammaOneCuspHeckeTrace1039a.log', 'SourceGammaOneCuspHeckeTrace1039b.exit', 'SourceGammaOneCuspHeckeTrace1039b.log', 'SourceGammaOneEndpointHecke.lean', 'SourceGammaOneEndpointHecke1068a.exit', 'SourceGammaOneEndpointHecke1068a.log', 'SourceGammaOneHeckeActualStabilizers.lean', 'SourceGammaOneHeckeActualStabilizers1062a.exit', 'SourceGammaOneHeckeActualStabilizers1062a.log', 'SourceGammaOneHeckeActualStabilizers1062b.exit', 'SourceGammaOneHeckeActualStabilizers1062b.log', 'SourceGammaOneHeckeAllFibers.lean', 'SourceGammaOneHeckeAllFibers1057a.exit', 'SourceGammaOneHeckeAllFibers1057a.log', 'SourceGammaOneHeckeAlphaGerms.lean', 'SourceGammaOneHeckeAlphaGerms1030a.exit', 'SourceGammaOneHeckeAlphaGerms1030a.log', 'SourceGammaOneHeckeAnalyticDivisor.lean', 'SourceGammaOneHeckeAnalyticDivisor1065a.exit', 'SourceGammaOneHeckeAnalyticDivisor1065a.log', 'SourceGammaOneHeckeAnalyticDivisor1065b.exit', 'SourceGammaOneHeckeAnalyticDivisor1065b.log', 'SourceGammaOneHeckeAnalyticDivisor1065c.exit', 'SourceGammaOneHeckeAnalyticDivisor1065c.log', 'SourceGammaOneHeckeAnalyticFiber.lean', 'SourceGammaOneHeckeAnalyticFiber1034a.exit', 'SourceGammaOneHeckeAnalyticFiber1034a.log', 'SourceGammaOneHeckeAnalyticFiber1034b.exit', 'SourceGammaOneHeckeAnalyticFiber1034b.log', 'SourceGammaOneHeckeAnalyticFiber1034c.exit', 'SourceGammaOneHeckeAnalyticFiber1034c.log', 'SourceGammaOneHeckeAnalyticFiber1034d.exit', 'SourceGammaOneHeckeAnalyticFiber1034d.log', 'SourceGammaOneHeckeAnalyticMapsAudit1.exit', 'SourceGammaOneHeckeAnalyticMapsAudit1.lean', 'SourceGammaOneHeckeAnalyticMapsAudit1.log', 'SourceGammaOneHeckeAnalyticMapsDependencyAudit1.exit', 'SourceGammaOneHeckeAnalyticMapsDependencyAudit1.lean', 'SourceGammaOneHeckeAnalyticMapsDependencyAudit1.log', 'SourceGammaOneHeckeAnalyticMapsScratchOwnership1035.exit', 'SourceGammaOneHeckeAnalyticMapsScratchOwnership1035.lean', 'SourceGammaOneHeckeAnalyticMapsScratchOwnership1035.log', 'SourceGammaOneHeckeAnalyticPlaces.lean', 'SourceGammaOneHeckeAnalyticPlaces1033a.exit', 'SourceGammaOneHeckeAnalyticPlaces1033a.log', 'SourceGammaOneHeckeAnalyticPlaces1033b.exit', 'SourceGammaOneHeckeAnalyticPlaces1033b.log', 'SourceGammaOneHeckeAnalyticPlaces1033c.exit', 'SourceGammaOneHeckeAnalyticPlaces1033c.log', 'SourceGammaOneHeckeAnalyticPlaces1033d.exit', 'SourceGammaOneHeckeAnalyticPlaces1033d.log', 'SourceGammaOneHeckeBetaGerms.lean', 'SourceGammaOneHeckeBetaGerms1032a.exit', 'SourceGammaOneHeckeBetaGerms1032a.log', 'SourceGammaOneHeckeBetaGerms1032b.exit', 'SourceGammaOneHeckeBetaGerms1032b.log', 'SourceGammaOneHeckeCharacters.lean', 'SourceGammaOneHeckeCharacters1045a.exit', 'SourceGammaOneHeckeCharacters1045a.log', 'SourceGammaOneHeckeCosetMultiplicity.lean', 'SourceGammaOneHeckeCosetMultiplicity1064a.exit', 'SourceGammaOneHeckeCosetMultiplicity1064a.log', 'SourceGammaOneHeckeCosetMultiplicity1064b.exit', 'SourceGammaOneHeckeCosetMultiplicity1064b.log', 'SourceGammaOneHeckeExactRamification.lean', 'SourceGammaOneHeckeExactRamification1058a.exit', 'SourceGammaOneHeckeExactRamification1058a.log', 'SourceGammaOneHeckeFiberPresentation.lean', 'SourceGammaOneHeckeFiberPresentation1054a.exit', 'SourceGammaOneHeckeFiberPresentation1054a.log', 'SourceGammaOneHeckeGammaZeroMap.lean', 'SourceGammaOneHeckeGammaZeroMap1051a.exit', 'SourceGammaOneHeckeGammaZeroMap1051a.log', 'SourceGammaOneHeckeGammaZeroMap1051b.exit', 'SourceGammaOneHeckeGammaZeroMap1051b.log', 'SourceGammaOneHeckeGammaZeroMap1051c.exit', 'SourceGammaOneHeckeGammaZeroMap1051c.log', 'SourceGammaOneHeckeGammaZeroPlaces.lean', 'SourceGammaOneHeckeGammaZeroPlaces1052a.exit', 'SourceGammaOneHeckeGammaZeroPlaces1052a.log', 'SourceGammaOneHeckeGenericFiber.lean', 'SourceGammaOneHeckeGenericFiber1055a.exit', 'SourceGammaOneHeckeGenericFiber1055a.log', 'SourceGammaOneHeckeGenericOrbits.lean', 'SourceGammaOneHeckeGenericOrbits1053a.exit', 'SourceGammaOneHeckeGenericOrbits1053a.log', 'SourceGammaOneHeckeGenericOrbits1053b.exit', 'SourceGammaOneHeckeGenericOrbits1053b.log', 'SourceGammaOneHeckeGeometricFibersAudit1b.exit', 'SourceGammaOneHeckeGeometricFibersAudit1b.lean', 'SourceGammaOneHeckeGeometricFibersAudit1b.log', 'SourceGammaOneHeckeGeometricFibersDependencyAudit1b.exit', 'SourceGammaOneHeckeGeometricFibersDependencyAudit1b.lean', 'SourceGammaOneHeckeGeometricFibersDependencyAudit1b.log', 'SourceGammaOneHeckeGeometricFibersScratchOwnership1060.exit', 'SourceGammaOneHeckeGeometricFibersScratchOwnership1060.log', 'SourceGammaOneHeckeGeometricFibersScratchOwnership1060b.exit', 'SourceGammaOneHeckeGeometricFibersScratchOwnership1060b.lean', 'SourceGammaOneHeckeGeometricFibersScratchOwnership1060b.log', 'SourceGammaOneHeckeJDegree.lean', 'SourceGammaOneHeckeJDegree1056a.exit', 'SourceGammaOneHeckeJDegree1056a.log', 'SourceGammaOneHeckePlaceOrbits.lean', 'SourceGammaOneHeckePlaceOrbits1059a.exit', 'SourceGammaOneHeckePlaceOrbits1059a.log', 'SourceGammaOneHeckePlaceOrbits1059b.exit', 'SourceGammaOneHeckePlaceOrbits1059b.log', 'SourceGammaOneHeckePlaceOrbits1059c.exit', 'SourceGammaOneHeckePlaceOrbits1059c.log', 'SourceGammaOneHeckePointTransition.lean', 'SourceGammaOneHeckePointTransition1042a.exit', 'SourceGammaOneHeckePointTransition1042a.log', 'SourceGammaOneHeckePrimitiveDerivative.lean', 'SourceGammaOneHeckePrimitiveDerivative1037a.exit', 'SourceGammaOneHeckePrimitiveDerivative1037a.log', 'SourceGammaOneHeckePrimitiveTrace.lean', 'SourceGammaOneHeckePrimitiveTrace1040a.exit', 'SourceGammaOneHeckePrimitiveTrace1040a.log', 'SourceGammaOneHeckePrimitiveTrace1040b.exit', 'SourceGammaOneHeckePrimitiveTrace1040b.log', 'SourceGammaOneHeckePrimitiveTraceAudit1.exit', 'SourceGammaOneHeckePrimitiveTraceAudit1.lean', 'SourceGammaOneHeckePrimitiveTraceAudit1.log', 'SourceGammaOneHeckePrimitiveTraceDependencyAudit1.exit', 'SourceGammaOneHeckePrimitiveTraceDependencyAudit1.lean', 'SourceGammaOneHeckePrimitiveTraceDependencyAudit1.log', 'SourceGammaOneHeckePrimitiveTraceScratchOwnership1041.exit', 'SourceGammaOneHeckePrimitiveTraceScratchOwnership1041.lean', 'SourceGammaOneHeckePrimitiveTraceScratchOwnership1041.log', 'SourceGammaOneHeckeStretchLaurent.lean', 'SourceGammaOneHeckeStretchLaurent1031a.exit', 'SourceGammaOneHeckeStretchLaurent1031a.log', 'SourceGammaOneHeckeTraceCosets.lean', 'SourceGammaOneHeckeTraceCosets1038a.exit', 'SourceGammaOneHeckeTraceCosets1038a.log', 'SourceGammaOneHeckeTraceCosets1038b.exit', 'SourceGammaOneHeckeTraceCosets1038b.log', 'SourceGammaOneHeckeUpperOrbits.lean', 'SourceGammaOneHeckeUpperOrbits1063a.exit', 'SourceGammaOneHeckeUpperOrbits1063a.log', 'SourceGammaOneHolomorphicH1Hecke.lean', 'SourceGammaOneHolomorphicH1Hecke1046a.exit', 'SourceGammaOneHolomorphicH1Hecke1046a.log', 'SourceGammaOneHolomorphicH1Hecke1046b.exit', 'SourceGammaOneHolomorphicH1Hecke1046b.log', 'SourceGammaOneHolomorphicH1HeckeAudit1.exit', 'SourceGammaOneHolomorphicH1HeckeAudit1.lean', 'SourceGammaOneHolomorphicH1HeckeAudit1.log', 'SourceGammaOneHolomorphicH1HeckeDependencyAudit1.exit', 'SourceGammaOneHolomorphicH1HeckeDependencyAudit1.lean', 'SourceGammaOneHolomorphicH1HeckeDependencyAudit1.log', 'SourceGammaOneHolomorphicH1HeckeScratchOwnership1047.exit', 'SourceGammaOneHolomorphicH1HeckeScratchOwnership1047.lean', 'SourceGammaOneHolomorphicH1HeckeScratchOwnership1047.log', 'SourceGammaOneInvariantDivisorPeriod.lean', 'SourceGammaOneInvariantDivisorPeriod1016a.exit', 'SourceGammaOneInvariantDivisorPeriod1016a.log', 'SourceGammaOneInvariantDivisorPeriod1016b.exit', 'SourceGammaOneInvariantDivisorPeriod1016b.log', 'SourceGammaOneJacobiInversion.lean', 'SourceGammaOneJacobiInversion1024a.exit', 'SourceGammaOneJacobiInversion1024a.log', 'SourceGammaOneJacobiInversion1024b.exit', 'SourceGammaOneJacobiInversion1024b.log', 'SourceGammaOneJacobiInversion1024c.exit', 'SourceGammaOneJacobiInversion1024c.log', 'SourceGammaOneJacobiInversion1029c.exit', 'SourceGammaOneJacobiInversion1029c.log', 'SourceGammaOnePeriodHeckeLattice.lean', 'SourceGammaOnePeriodHeckeLattice1049a.exit', 'SourceGammaOnePeriodHeckeLattice1049a.log', 'SourceGammaOnePeriodHeckeLattice1049b.exit', 'SourceGammaOnePeriodHeckeLattice1049b.log', 'SourceGammaOnePeriodLatticeHeckeAudit1.exit', 'SourceGammaOnePeriodLatticeHeckeAudit1.lean', 'SourceGammaOnePeriodLatticeHeckeAudit1.log', 'SourceGammaOnePeriodLatticeHeckeDependencyAudit1b.exit', 'SourceGammaOnePeriodLatticeHeckeDependencyAudit1b.lean', 'SourceGammaOnePeriodLatticeHeckeDependencyAudit1b.log', 'SourceGammaOnePeriodLatticeHeckeScratchOwnership1050b.exit', 'SourceGammaOnePeriodLatticeHeckeScratchOwnership1050b.lean', 'SourceGammaOnePeriodLatticeHeckeScratchOwnership1050b.log', 'SourceGammaOnePeriodNormalization.lean', 'SourceGammaOnePeriodNormalization1043a.exit', 'SourceGammaOnePeriodNormalization1043a.log', 'SourceGammaOnePicardHeckeDivisors.lean', 'SourceGammaOnePicardHeckeDivisors1067a.exit', 'SourceGammaOnePicardHeckeDivisors1067a.log', 'SourceGammaOnePicardHeckeDivisors1067b.exit', 'SourceGammaOnePicardHeckeDivisors1067b.log', 'SourceGammaOnePicardHeckeDivisors1067c.exit', 'SourceGammaOnePicardHeckeDivisors1067c.log', 'SourceGammaOnePicardPeriodEquiv.lean', 'SourceGammaOnePicardPeriodEquiv1027a.exit', 'SourceGammaOnePicardPeriodEquiv1027a.log', 'SourceGammaOnePicardPeriodEquiv1029c.exit', 'SourceGammaOnePicardPeriodEquiv1029c.log', 'SourceGammaOnePicardPeriodEquivalenceAudit1d.exit', 'SourceGammaOnePicardPeriodEquivalenceAudit1d.lean', 'SourceGammaOnePicardPeriodEquivalenceAudit1d.log', 'SourceGammaOnePicardPeriodEquivalenceDependencyAudit1d.exit', 'SourceGammaOnePicardPeriodEquivalenceDependencyAudit1d.lean', 'SourceGammaOnePicardPeriodEquivalenceDependencyAudit1d.log', 'SourceGammaOnePicardPeriodEquivalenceScratchOwnership1029d.exit', 'SourceGammaOnePicardPeriodEquivalenceScratchOwnership1029d.lean', 'SourceGammaOnePicardPeriodEquivalenceScratchOwnership1029d.log', 'SourceGammaOnePicardPeriodEquivalenceValueProbe1028.exit', 'SourceGammaOnePicardPeriodEquivalenceValueProbe1028.log', 'SourceGammaOnePicardPeriodHecke.lean', 'SourceGammaOnePicardPeriodHecke1069a.exit', 'SourceGammaOnePicardPeriodHecke1069a.log', 'SourceGammaOnePicardPeriodHeckeAudit1.exit', 'SourceGammaOnePicardPeriodHeckeAudit1.lean', 'SourceGammaOnePicardPeriodHeckeAudit1.log', 'SourceGammaOnePicardPeriodHeckeDependencyAudit1.exit', 'SourceGammaOnePicardPeriodHeckeDependencyAudit1.lean', 'SourceGammaOnePicardPeriodHeckeDependencyAudit1.log', 'SourceGammaOnePicardPeriodHeckeScratchOwnership1070.exit', 'SourceGammaOnePicardPeriodHeckeScratchOwnership1070.lean', 'SourceGammaOnePicardPeriodHeckeScratchOwnership1070.log', 'SourceGammaOnePicardPeriodKernel.lean', 'SourceGammaOnePicardPeriodKernel1026a.exit', 'SourceGammaOnePicardPeriodKernel1026a.log', 'SourceGammaOnePicardPeriodKernel1026b.exit', 'SourceGammaOnePicardPeriodKernel1026b.log', 'SourceGammaOnePicardPeriodKernel1029c.exit', 'SourceGammaOnePicardPeriodKernel1029c.log', 'SourceGammaOnePrincipalMeromorphicRealization.lean', 'SourceGammaOnePrincipalMeromorphicRealization1017a.exit', 'SourceGammaOnePrincipalMeromorphicRealization1017a.log', 'SourceGammaOnePrincipalMeromorphicRealization1017b.exit', 'SourceGammaOnePrincipalMeromorphicRealization1017b.log', 'SourceGammaOnePrincipalMeromorphicRealization1017c.exit', 'SourceGammaOnePrincipalMeromorphicRealization1017c.log', 'SourceGammaOneScalarHeckePeriods.lean', 'SourceGammaOneScalarHeckePeriods1044a.exit', 'SourceGammaOneScalarHeckePeriods1044a.log', 'SourceGammaOneWeightTwoHeckeCosets.lean', 'SourceGammaOneWeightTwoHeckeCosets1036a.exit', 'SourceGammaOneWeightTwoHeckeCosets1036a.log', 'SourceGammaOneWeightTwoHeckeCosets1036b.exit', 'SourceGammaOneWeightTwoHeckeCosets1036b.log', 'SourceWeightTwoEndpointImage.lean', 'SourceWeightTwoEndpointImage1021a.exit', 'SourceWeightTwoEndpointImage1021a.log', 'SourceWeightTwoEndpointImage1021b.exit', 'SourceWeightTwoEndpointImage1021b.log', 'SourceWeightTwoEndpointImage1029b.exit', 'SourceWeightTwoEndpointImage1029b.log', 'SourceWeightTwoEndpointImage1029c.exit', 'SourceWeightTwoEndpointImage1029c.log', 'SourceWeightTwoEndpointOpenImage.lean', 'SourceWeightTwoEndpointOpenImage1022a.exit', 'SourceWeightTwoEndpointOpenImage1022a.log', 'SourceWeightTwoEndpointOpenImage1022b.exit', 'SourceWeightTwoEndpointOpenImage1022b.log', 'SourceWeightTwoEndpointOpenImage1022c.exit', 'SourceWeightTwoEndpointOpenImage1022c.log', 'SourceWeightTwoEndpointOpenImage1029c.exit', 'SourceWeightTwoEndpointOpenImage1029c.log', 'SourceWeightTwoEvaluationFrame.lean', 'SourceWeightTwoEvaluationFrame1020a.exit', 'SourceWeightTwoEvaluationFrame1020a.log', 'SourceWeightTwoEvaluationFrame1020b.exit', 'SourceWeightTwoEvaluationFrame1020b.log', 'SourceWeightTwoEvaluationFrame1020c.exit', 'SourceWeightTwoEvaluationFrame1020c.log', 'SourceWeightTwoEvaluationFrame1020d.exit', 'SourceWeightTwoEvaluationFrame1020d.log', 'SourceWeightTwoEvaluationFrame1029b.exit', 'SourceWeightTwoEvaluationFrame1029b.log', 'SourceWeightTwoEvaluationFrame1029c.exit', 'SourceWeightTwoEvaluationFrame1029c.log', 'SourceWeightTwoJacobiInversion.lean', 'SourceWeightTwoJacobiInversion1023a.exit', 'SourceWeightTwoJacobiInversion1023a.log', 'SourceWeightTwoJacobiInversion1023b.exit', 'SourceWeightTwoJacobiInversion1023b.log', 'SourceWeightTwoJacobiInversion1029c.exit', 'SourceWeightTwoJacobiInversion1029c.log', 'audit_gamma_one_analytic_abel_kernel_1019.ps1', 'audit_gamma_one_hecke_analytic_maps_1035.ps1', 'audit_gamma_one_hecke_geometric_fibers_1060.ps1', 'audit_gamma_one_hecke_geometric_fibers_1060b.ps1', 'audit_gamma_one_hecke_primitive_trace_1041.ps1', 'audit_gamma_one_holomorphic_h1_hecke_1047.ps1', 'audit_gamma_one_period_lattice_hecke_1050.ps1', 'audit_gamma_one_period_lattice_hecke_1050b.ps1', 'audit_gamma_one_picard_period_equivalence_1029.ps1', 'audit_gamma_one_picard_period_equivalence_1029b.ps1', 'audit_gamma_one_picard_period_equivalence_1029c.ps1', 'audit_gamma_one_picard_period_equivalence_1029d.ps1', 'audit_gamma_one_picard_period_hecke_1070.ps1', 'consumers1017.txt', 'consumers1041.txt', 'consumers1056.txt', 'consumers1066.txt', 'docs1017.py', 'docs1056.py', 'docs1066.py', 'foundation1017-console.log', 'foundation1041-console.log', 'foundation1056-console.log', 'foundation1066-console.log', 'gamma-one-picard-hecke-comparison-promotion-route-1070.json', 'modules1017.json', 'modules1041.json', 'modules1056.json', 'modules1066.json', 'paper1017-console.log', 'paper1041-console.log', 'paper1056-console.log', 'paper1066-console.log', 'prepare_gamma_one_picard_period_hecke_audit_1070.py', 'record1017.py', 'record1041.py', 'record1056.py', 'record1066.py', 'record_source_gamma_one_analytic_abel_kernel_1019.py', 'record_source_gamma_one_hecke_analytic_maps_1035.py', 'record_source_gamma_one_hecke_geometric_fibers_1060.py', 'record_source_gamma_one_hecke_geometric_fibers_1060b.py', 'record_source_gamma_one_hecke_primitive_trace_1041.py', 'record_source_gamma_one_holomorphic_h1_hecke_1047.py', 'record_source_gamma_one_period_lattice_hecke_1050.py', 'record_source_gamma_one_period_lattice_hecke_1050b.py', 'record_source_gamma_one_picard_period_equivalence_1029.py', 'record_source_gamma_one_picard_period_equivalence_1029b.py', 'record_source_gamma_one_picard_period_equivalence_1029c.py', 'record_source_gamma_one_picard_period_equivalence_1029d.py', 'record_source_gamma_one_picard_period_hecke_1070.py', 'register1017.py', 'register1041.py', 'register1056.py', 'register1066.py', 'registrations1017.json', 'registrations1041.json', 'registrations1056.json', 'registrations1066.json', 'section1017.txt', 'section1041.txt', 'section1056.txt', 'section1066.txt', 'source-gamma-one-analytic-abel-kernel-1-audit-config.json', 'source-gamma-one-analytic-abel-kernel-1-reuse-review-20261027.json', 'source-gamma-one-analytic-abel-kernel-1-scratch-receipt.json', 'source-gamma-one-analytic-abel-kernel-audit-route-1019.json', 'source-gamma-one-forward-abel-route-1016.json', 'source-gamma-one-geometric-fiber-reuse-route-1051.json', 'source-gamma-one-hecke-analytic-maps-1-audit-config.json', 'source-gamma-one-hecke-analytic-maps-1-reuse-review-20261027.json', 'source-gamma-one-hecke-analytic-maps-1-scratch-receipt.json', 'source-gamma-one-hecke-analytic-maps-audit-route-1035.json', 'source-gamma-one-hecke-analytic-maps-route-1030.json', 'source-gamma-one-hecke-coset-multiplicity-route-1062.json', 'source-gamma-one-hecke-geometric-fibers-1b-audit-config.json', 'source-gamma-one-hecke-geometric-fibers-1b-reuse-review-20261027.json', 'source-gamma-one-hecke-geometric-fibers-1b-scratch-receipt.json', 'source-gamma-one-hecke-geometric-fibers-audit-route-1060.json', 'source-gamma-one-hecke-primitive-route-1036.json', 'source-gamma-one-hecke-primitive-trace-1-audit-config.json', 'source-gamma-one-hecke-primitive-trace-1-reuse-review-20261027.json', 'source-gamma-one-hecke-primitive-trace-1-scratch-receipt.json', 'source-gamma-one-hecke-primitive-trace-audit-route-1041.json', 'source-gamma-one-holomorphic-h1-hecke-1-audit-config.json', 'source-gamma-one-holomorphic-h1-hecke-1-reuse-review-20261027.json', 'source-gamma-one-holomorphic-h1-hecke-1-scratch-receipt.json', 'source-gamma-one-holomorphic-h1-hecke-audit-route-1047.json', 'source-gamma-one-period-hecke-route-1042.json', 'source-gamma-one-period-lattice-hecke-1b-audit-config.json', 'source-gamma-one-period-lattice-hecke-1b-reuse-review-20261027.json', 'source-gamma-one-period-lattice-hecke-1b-scratch-receipt.json', 'source-gamma-one-period-lattice-hecke-accessors-1050b.json', 'source-gamma-one-period-lattice-hecke-audit-route-1050.json', 'source-gamma-one-period-lattice-hecke-route-1048.json', 'source-gamma-one-picard-period-equivalence-1d-audit-config.json', 'source-gamma-one-picard-period-equivalence-1d-reuse-review-20261027.json', 'source-gamma-one-picard-period-equivalence-1d-scratch-receipt.json', 'source-gamma-one-picard-period-equivalence-audit-route-1029.json', 'source-gamma-one-picard-period-hecke-1-audit-config.json', 'source-gamma-one-picard-period-hecke-1-reuse-review-20261027.json', 'source-gamma-one-picard-period-hecke-1-scratch-receipt.json', 'source-gamma-one-picard-period-hecke-audit-route-1070.json', 'source-gamma-one-picard-period-route-1026.json', 'source-gamma-one-positive-weight-reuse-1057.json', 'source-gamma-one-scalar-period-reuse-1044.json', 'source-weight-two-jacobi-inversion-route-1020.json', 'status1017.txt', 'status1041.txt', 'status1056.txt', 'status1066.txt']]
for folder in ['anthropic-flt-residual-closure-20261020', 'anthropic-flt-residual-reuse-20261020', 'anthropic-flt-reuse-20261020', 'arithmetic-reuse-20261020', 'blgg-source-review-20261019', 'cht-reuse-20261019', 'class-generator-source-20261016', 'class-norm-reuse-20261023', 'differential-reuse-20261020', 'elliptic-function-field-reuse-20261023', 'elliptic-infinity-reuse-20261023', 'elliptic-translation-reuse-20261023', 'etale-reuse-20261020', 'gamma-one-central-sign-decidability-1061a', 'gamma-one-coset-multiplicity-translation-binder-1064a', 'gamma-one-cusp-trace-complex-scalars-1048a', 'gamma-one-cusp-trace-matrix-orientation-1039a', 'gamma-one-divisor-evaluation-defeq-1065b', 'gamma-one-divisor-sum-defeq-1065a', 'gamma-one-forward-period-add-order-1016a', 'gamma-one-generic-orbit-subgroup-type-1053a', 'gamma-one-h1-character-defeq-1046a', 'gamma-one-hecke-beta-composition-1032a', 'gamma-one-hecke-cosets-inverse-namespace-1036a', 'gamma-one-hecke-fiber-evaluation-aliases-1034b', 'gamma-one-hecke-fiber-explicit-evaluation-1034c', 'gamma-one-hecke-fiber-field-defeq-1034a', 'gamma-one-hecke-orbit-representative-defeq-1059a', 'gamma-one-hecke-orbit-unused-parameters-1059b', 'gamma-one-hecke-places-explicit-parameters-1033a', 'gamma-one-hecke-places-membership-defeq-1033c', 'gamma-one-hecke-places-pipe-encoding-1033b', 'gamma-one-hecke-trace-coset-hom-laws-1038a', 'gamma-one-jacobi-local-instance-syntax-1024a', 'gamma-one-jacobi-unused-simp-1024b', 'gamma-one-level-one-membership-1051a', 'gamma-one-level-one-membership-defeq-1051b', 'gamma-one-period-lattice-membership-1049a', 'gamma-one-picard-divisor-map-domain-1067b', 'gamma-one-picard-divisor-map-sum-1067a', 'gamma-one-picard-map-zero-1025b', 'gamma-one-picard-map-zero-inference-1025c', 'gamma-one-picard-notation-parser-1025a', 'gamma-one-picard-period-docblame-1029', 'gamma-one-picard-period-line-endings-1029b', 'gamma-one-picard-period-notation-projection-1026a', 'gamma-one-primitive-uniqueness-reuse-1040a', 'gamma-one-principal-realization-beta-1017b', 'gamma-one-principal-realization-import-1017a', 'gamma-one-stabilizer-subgroup-type-import-1062a', 'lean-reuse-refresh-20261022', 'mathlib-matrix-density-reuse-20261019', 'nyll-nondegeneracy-20261024', 'odd-isogeny-route-20261023', 'odd-normality-route-20261023', 'odd-quotient-reuse-20261023', 'reuse-odd-product-route-20261023', 'reuse-refresh-20261018', 'reuse-refresh-20261019', 'reuse-torsion-reduction-20261023', 'source-sl-generation-reuse-20261020', 'source-sl-reuse-20261020', 'source-unipotent-reuse-20261020', 'subspace-determinant-reuse-20261019', 'tau-ceti-integral-coordinate-20261019', 'tau-ceti-reuse-20261019', 'tau-yone-reuse-20261020', 'vaca22-riemann-roch-20261021', 'weight-two-endpoint-function-sub-1021a', 'weight-two-endpoint-open-analytic-add-1022b', 'weight-two-endpoint-open-composition-1022a', 'weight-two-evaluation-complex-smul-1020b', 'weight-two-evaluation-sum-1020a', 'weight-two-evaluation-unused-index-1020c', 'weight-two-jacobi-image-coercion-1023a']:
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
supplemental_review_path=r/archive_rel/'gamma-one-picard-hecke-comparison-promotion-route-1070.json'

audit = r / "Extension/Dubon2026/Audit.lean"
at = audit.read_text(encoding="utf-8")
for n in queries:
    assert not re.search(r"``" + re.escape(n) + r"(?=[,\s])", at)
tm, dm = "\n]\n\nprivate def publicConstructions", "\n]\n\nprivate def runAudit"
assert at.count(tm) == at.count(dm) == 1
at = at.replace(tm, "".join("\n  ,``" + n for n in theorems) + tm, 1)
at = at.replace(dm, "".join("\n  ," + chr(96)*2 + n for n in defs) + dm, 1)
research_path = r / "Tools/lean-reuse-audit-20261020.json"
reuse_path = r / "Tools/source-gamma-one-picard-hecke-comparison.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt8821"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> arithmetic realization of original finite Gamma1 homogeneous-coefficient Hecke characters -> full/parabolic, transpose, diamond and Picard/H1 comparison -> actual Picard-period equivalence and prime Hecke compatibility.'
discharged = 'The actual original complex Gamma1 Picard group is now identified with the original integer-period quotient by a proved additive equivalence. The forward Abel implication and finite Jacobi inversion discharge its kernel and surjectivity assumptions. The native holomorphic H1 period map intertwines the actual constant-coefficient Hecke operator for every nonzero index. The dual cusp trace preserves the original integer-period lattice. Actual intersection-curve orbit separation, exact ramification and coset multiplicity identify literal prime beta pullback followed by alpha pushforward with the analytic coset divisor sum, including elliptic fibers. The degree-zero hypothesis cancels the explicitly computed endpoint basepoint term. Consequently the original Picard-period equivalence intertwines the literal algebraic prime Hecke correspondence and the native dual cusp action, including primes dividing the level. No Picard equivalence, Hecke compatibility, fiber multiplicity, lattice stability or degree-zero cancellation certificate remains assumed in these complex comparisons.'
boundary = 'This proves the complex additive Picard-period and prime Hecke comparison and the holomorphic constant-coefficient H1 comparison. Full parabolic, diamond, transpose and arithmetic compatibility, coefficient-field transport, Frobenius/inertia, arithmetic realization of original finite homogeneous-coefficient Gamma1 characters, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain. Finite characters, complex semisimplicity, Witt coefficients and universal deformation rings do not supply a characteristic-zero lift. 16/20; DUB-17--20 OPEN; all twenty acceptance gates unchanged.'
status = 'The forty-six-module actual Gamma1 Picard and Hecke comparison scope passes 128 public axiom queries, 216 exhaustive scratch theorem checks, sixteen linters per module and eight declaration-value audits with 189 required dependency checks, with zero diagnostics. Production aggregate, focused audits and sequential foundation/paper verification of the 8,867-module scope are pending.'
route = 'Reuse the October 27 fixed-revision source assessment and the existing local foundations. Native endpoint primitives and Jacobi inversion, literal divisor pull/push, positive ramification-weight counting, exact coset stabilizer counting, native cusp traces and H1 cocycles provide the required chain. The short all-fiber route uses generic separation and exact field degree to force every positive ramification bound to equality. Additive Finsupp extensionality extends the point formula, and degree zero removes the basepoint term. No separate intersection-curve modular-form separation theory, general quotient atlas or incidental correspondence abstraction is introduced. All used and failed evidence is retained; frozen mathematical bodies are promoted by import qualification only.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Actual original Gamma1 Picard and Hecke comparison (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 8,821-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
corrections = []
count = sum(z['exhaustiveTheorems'] for z in certs)
assert count == 216

docpaths = list(dict.fromkeys(r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]))
for f in docpaths:
    assert "\n\n" in f.read_text(encoding="utf-8")
readmes = [(r.parent / "README.md", "Current Project 83 status ("), (repo / "README.md", "Project 83 has an ")]
for f, prefix in readmes:
    assert sum(line.startswith(prefix) for line in f.read_text(encoding="utf-8").splitlines()) == 1
arch = r / "Dubon Architecture.md"
edge = '  GAMMAONEPRINCIPAL8821["Original integral period class implies literal principalness for every finite degree-zero Gamma1 analytic divisor. Actual residue differential, meromorphic function, multiplier and cusp inputs constructed. Forward implication, full Picard/Hecke/H1, all-weight association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourceGammaOnePicardHeckeComparisonProductionAudit8867.lean',p/'source-gamma-one-picard-hecke-comparison-8867-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production8867.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/gamma-one-principal-divisor-20261027-1015'
registered = {row['path'] for row in c['files']}
for priorFile in priorArchive.iterdir():
    rel = priorFile.relative_to(r).as_posix()
    if priorFile.is_file() and rel not in registered:
        c['files'].append({'path': rel, 'role': 'Tools'})

reportSource = p / 'Dubon Picard Hecke Reuse Assessment 2026-10-27.md'
assert sha(reportSource) == '7E3FC20D71B31BBE9B6787BC07B2FB28565D8855D114F7DF500398EEBB4E6BF1'
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
    "productionModules": 8867, "modules": newmods, "queries": queries,
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
arch.write_text(arch.read_text(encoding='utf-8').replace(edge,'  GAMMAONEPRINCIPAL8821["Actual Gamma1 finite-divisor principalness converse proved (DUB-17/18)"] --> GAMMAONEPICARDHECKE8867\n  GAMMAONEPICARDHECKE8867["Actual complex Picard-period equivalence, holomorphic H1 Hecke compatibility and literal prime Picard Hecke compatibility proved. Full parabolic, diamond, transpose, arithmetic, all-weight association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'),encoding='utf-8')



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Actual original Gamma1 Picard and Hecke comparison - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-gamma-one-picard-hecke-comparison.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub('  logInfo m!".*"\\n', '  logInfo m!"SOURCE GAMMA ONE PICARD HECKE COMPARISON AUDIT PASS: {count} theorems including private/generated declarations. Actual original complex Picard-period and prime Hecke compatibility, plus holomorphic H1 Hecke compatibility. Full parabolic/diamond/transpose/arithmetic and all-weight association remain; 16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourceGammaOnePicardHeckeComparisonProductionAudit8867.lean").write_text(out, encoding="utf-8")
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
    target = p / (source.stem + "Production8867.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
(p / "source-gamma-one-picard-hecke-comparison-8867-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 8867, "increment": 46, "queries": 128,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
