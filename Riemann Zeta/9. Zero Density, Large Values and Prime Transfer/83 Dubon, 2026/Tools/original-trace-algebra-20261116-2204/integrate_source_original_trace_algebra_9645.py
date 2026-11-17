from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 9611
assert d["appliedSourcePrimitiveJointArithmetic"]["receipt9611"]["exit"] == 0
assert (p / "paper-verification-9611-console.exit").read_text().strip() == "0"
assert (r/'Tools/primitive-joint-arithmetic-20261116-2149/canonical-evidence-9611.json').exists()
key = "appliedSourceOriginalTraceAlgebra"
assert key not in d
digests = {'source-gammaone-primitive-trace-1-scratch-receipt.json': 'CBCF607DCE97D418ACDA3B1AEFA07D93238AF10C0003B4451E440F8E284F367A', 'source-original-local-trace-1-scratch-receipt.json': 'C6A8C67F3CD51FC43E1E4B7B2700AEE1CD684131E115D2BA9AE17D2734C8D1D1', 'source-original-trace-algebra-1-scratch-receipt.json': 'B59EA0D313E663C9EE5E2EE1DC975EAC827F1C9A6EB26908EF59984042DFCAEF'}

for name, digest in digests.items():
    assert sha(p / name) == digest
certs = [json.loads((p / name).read_text(encoding="utf-8")) for name in digests]
mods = [m for z in certs for m in z["modules"]]
queries = [q for z in certs for q in z["queries"]]
theorems = [q for z in certs for q in z["theoremRegistrations"]]
defs = [q for z in certs for q in z["constructionRegistrations"]]
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (34, 34, 76, 61, 15)
omitted = []
assert not set(mods).intersection(c["productionModules"])
mapping = {m: "Dubon2026." + m for m in c["productionModules"] + mods}
mapping["SourceGammaOneFiniteDivisorReciprocityAssembled"] = "Dubon2026.SourceGammaOneFiniteDivisorReciprocity"
# Qualify versioned imports from independently audited adjacent scratch scopes.
# Only a suffix naming a registered module is accepted; bodies/comments stay frozen.
for cert in certs:
    for item in cert['files']:
        for imported in re.findall(r'^import (\S+)',Path(item['path']).read_text(encoding='utf-8'),re.M):
            if imported in mapping or imported.startswith(('Dubon2026.','Mathlib.')):continue
            match=re.fullmatch(r'(Source.+?)([0-9]{4}[a-z]?)',imported)
            if match and match[1] in mods:mapping[imported]='Dubon2026.'+match[1]
for cert in certs:
    for source in [Path(cert['dependencyAuditLog']).with_suffix('.lean')] + [Path(x['path']) for x in cert['files']]:
        for imported in re.findall(r'\b(Source[A-Za-z0-9_]+)', source.read_text(encoding='utf-8')):
            match = re.fullmatch(r'(Source.+?)([0-9]{4}[a-z]?)', imported)
            if match and match[1] in mapping: mapping[imported] = mapping[match[1]]
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
archive_rel='Tools/original-trace-algebra-20261116-2204'
evidence=[p/n for n in ['Dubon Original Local Trace Assessment 2026-11-16.md', 'Dubon Original Trace Algebra Assessment 2026-11-16.md', 'SourceAbsoluteContinuousLocalFactor-2165.exit', 'SourceAbsoluteContinuousLocalFactor-2165.log', 'SourceAbsoluteContinuousLocalFactor.lean', 'SourceAbsoluteContinuousLocalFactor2162a.exit', 'SourceAbsoluteContinuousLocalFactor2162a.lean.txt', 'SourceAbsoluteContinuousLocalFactor2162a.log', 'SourceAbsoluteContinuousLocalFactor2162b.exit', 'SourceAbsoluteContinuousLocalFactor2162b.lean', 'SourceAbsoluteContinuousLocalFactor2162b.log', 'SourceAbsoluteCyclicFrobeniusEquality-2165.exit', 'SourceAbsoluteCyclicFrobeniusEquality-2165.log', 'SourceAbsoluteCyclicFrobeniusEquality.lean', 'SourceAbsoluteCyclicFrobeniusEquality2163a.exit', 'SourceAbsoluteCyclicFrobeniusEquality2163a.lean.txt', 'SourceAbsoluteCyclicFrobeniusEquality2163a.log', 'SourceAbsoluteCyclicFrobeniusEquality2163b.exit', 'SourceAbsoluteCyclicFrobeniusEquality2163b.lean', 'SourceAbsoluteCyclicFrobeniusEquality2163b.log', 'SourceAbsoluteNormFrobeniusConjugate-2165.exit', 'SourceAbsoluteNormFrobeniusConjugate-2165.log', 'SourceAbsoluteNormFrobeniusConjugate.lean', 'SourceAbsoluteNormFrobeniusConjugate2150a.exit', 'SourceAbsoluteNormFrobeniusConjugate2150a.lean.txt', 'SourceAbsoluteNormFrobeniusConjugate2150a.log', 'SourceAbsoluteNormFrobeniusConjugate2150b.exit', 'SourceAbsoluteNormFrobeniusConjugate2150b.lean.txt', 'SourceAbsoluteNormFrobeniusConjugate2150b.log', 'SourceAbsoluteNormFrobeniusConjugate2150c.exit', 'SourceAbsoluteNormFrobeniusConjugate2150c.lean.txt', 'SourceAbsoluteNormFrobeniusConjugate2150c.log', 'SourceAbsoluteNormFrobeniusConjugate2150d.exit', 'SourceAbsoluteNormFrobeniusConjugate2150d.lean.txt', 'SourceAbsoluteNormFrobeniusConjugate2150d.log', 'SourceAbsoluteNormFrobeniusConjugate2150e.exit', 'SourceAbsoluteNormFrobeniusConjugate2150e.lean.txt', 'SourceAbsoluteNormFrobeniusConjugate2150e.log', 'SourceAbsoluteNormFrobeniusConjugate2150f.exit', 'SourceAbsoluteNormFrobeniusConjugate2150f.lean', 'SourceAbsoluteNormFrobeniusConjugate2150f.log', 'SourceAbsoluteTracePairComparison-2165.exit', 'SourceAbsoluteTracePairComparison-2165.log', 'SourceAbsoluteTracePairComparison.lean', 'SourceAbsoluteTracePairComparison2166a.exit', 'SourceAbsoluteTracePairComparison2166a.lean', 'SourceAbsoluteTracePairComparison2166a.log', 'SourceActualTraceAlgebra-2190.exit', 'SourceActualTraceAlgebra-2190.log', 'SourceActualTraceAlgebra.lean', 'SourceActualTraceAlgebra2187a.exit', 'SourceActualTraceAlgebra2187a.lean', 'SourceActualTraceAlgebra2187a.log', 'SourceAdicFunctionContinuity-2176.exit', 'SourceAdicFunctionContinuity-2176.log', 'SourceAdicFunctionContinuity.lean', 'SourceAdicFunctionContinuity2170a.exit', 'SourceAdicFunctionContinuity2170a.lean.txt', 'SourceAdicFunctionContinuity2170a.log', 'SourceAdicFunctionContinuity2170b.exit', 'SourceAdicFunctionContinuity2170b.lean', 'SourceAdicFunctionContinuity2170b.log', 'SourceCompatibleTraceLift-2176.exit', 'SourceCompatibleTraceLift-2176.log', 'SourceCompatibleTraceLift.lean', 'SourceCompatibleTraceLift2171a.exit', 'SourceCompatibleTraceLift2171a.lean', 'SourceCompatibleTraceLift2171a.log', 'SourceGammaOneCompatibleAdicTrace-2165.exit', 'SourceGammaOneCompatibleAdicTrace-2165.log', 'SourceGammaOneCompatibleAdicTrace.lean', 'SourceGammaOneCompatibleAdicTrace2164a-interruption.json', 'SourceGammaOneCompatibleAdicTrace2164a.lean.txt', 'SourceGammaOneCompatibleAdicTrace2164a.log', 'SourceGammaOneCompatibleAdicTrace2164b.exit', 'SourceGammaOneCompatibleAdicTrace2164b.lean', 'SourceGammaOneCompatibleAdicTrace2164b.log', 'SourceGammaOneConstructedLocalTrace-2176.exit', 'SourceGammaOneConstructedLocalTrace-2176.log', 'SourceGammaOneConstructedLocalTrace.lean', 'SourceGammaOneConstructedLocalTrace2173a.exit', 'SourceGammaOneConstructedLocalTrace2173a.lean.txt', 'SourceGammaOneConstructedLocalTrace2173a.log', 'SourceGammaOneConstructedLocalTrace2173b.exit', 'SourceGammaOneConstructedLocalTrace2173b.lean', 'SourceGammaOneConstructedLocalTrace2173b.log', 'SourceGammaOneOriginalAdicTrace-2165.exit', 'SourceGammaOneOriginalAdicTrace-2165.log', 'SourceGammaOneOriginalAdicTrace.lean', 'SourceGammaOneOriginalAdicTrace2160a.exit', 'SourceGammaOneOriginalAdicTrace2160a.lean', 'SourceGammaOneOriginalAdicTrace2160a.log', 'SourceGammaOneOriginalLocalTrace-2176.exit', 'SourceGammaOneOriginalLocalTrace-2176.log', 'SourceGammaOneOriginalLocalTrace.lean', 'SourceGammaOneOriginalLocalTrace2172a.exit', 'SourceGammaOneOriginalLocalTrace2172a.lean', 'SourceGammaOneOriginalLocalTrace2172a.log', 'SourceGammaOneOriginalTraceAlgebra-2190.exit', 'SourceGammaOneOriginalTraceAlgebra-2190.log', 'SourceGammaOneOriginalTraceAlgebra.lean', 'SourceGammaOneOriginalTraceAlgebra2188a.exit', 'SourceGammaOneOriginalTraceAlgebra2188a.lean', 'SourceGammaOneOriginalTraceAlgebra2188a.log', 'SourceGammaOnePrimitiveJointDeterminant-2165.exit', 'SourceGammaOnePrimitiveJointDeterminant-2165.log', 'SourceGammaOnePrimitiveJointDeterminant.lean', 'SourceGammaOnePrimitiveJointDeterminant2146a.exit', 'SourceGammaOnePrimitiveJointDeterminant2146a.lean.txt', 'SourceGammaOnePrimitiveJointDeterminant2146a.log', 'SourceGammaOnePrimitiveJointDeterminant2146b.exit', 'SourceGammaOnePrimitiveJointDeterminant2146b.lean', 'SourceGammaOnePrimitiveJointDeterminant2146b.log', 'SourceGammaOnePrimitiveJointHeckeTrace-2165.exit', 'SourceGammaOnePrimitiveJointHeckeTrace-2165.log', 'SourceGammaOnePrimitiveJointHeckeTrace.lean', 'SourceGammaOnePrimitiveJointHeckeTrace2157a.exit', 'SourceGammaOnePrimitiveJointHeckeTrace2157a.lean.txt', 'SourceGammaOnePrimitiveJointHeckeTrace2157a.log', 'SourceGammaOnePrimitiveJointHeckeTrace2157b.exit', 'SourceGammaOnePrimitiveJointHeckeTrace2157b.lean', 'SourceGammaOnePrimitiveJointHeckeTrace2157b.log', 'SourceGammaOnePrimitiveJointTrace-2165.exit', 'SourceGammaOnePrimitiveJointTrace-2165.log', 'SourceGammaOnePrimitiveJointTrace.lean', 'SourceGammaOnePrimitiveJointTrace2147a.exit', 'SourceGammaOnePrimitiveJointTrace2147a.lean.txt', 'SourceGammaOnePrimitiveJointTrace2147a.log', 'SourceGammaOnePrimitiveJointTrace2147b.exit', 'SourceGammaOnePrimitiveJointTrace2147b.lean', 'SourceGammaOnePrimitiveJointTrace2147b.log', 'SourceGammaOnePrimitiveJointTraceConjugation-2165.exit', 'SourceGammaOnePrimitiveJointTraceConjugation-2165.log', 'SourceGammaOnePrimitiveJointTraceConjugation.lean', 'SourceGammaOnePrimitiveJointTraceConjugation2153a.exit', 'SourceGammaOnePrimitiveJointTraceConjugation2153a.lean.txt', 'SourceGammaOnePrimitiveJointTraceConjugation2153a.log', 'SourceGammaOnePrimitiveJointTraceConjugation2153b.exit', 'SourceGammaOnePrimitiveJointTraceConjugation2153b.lean', 'SourceGammaOnePrimitiveJointTraceConjugation2153b.log', 'SourceGammaOnePrimitiveJointTraceFrobenius-2165.exit', 'SourceGammaOnePrimitiveJointTraceFrobenius-2165.log', 'SourceGammaOnePrimitiveJointTraceFrobenius.lean', 'SourceGammaOnePrimitiveJointTraceFrobenius2151a.exit', 'SourceGammaOnePrimitiveJointTraceFrobenius2151a.lean', 'SourceGammaOnePrimitiveJointTraceFrobenius2151a.log', 'SourceGammaOnePrimitiveJointTraceIdentities-2165.exit', 'SourceGammaOnePrimitiveJointTraceIdentities-2165.log', 'SourceGammaOnePrimitiveJointTraceIdentities.lean', 'SourceGammaOnePrimitiveJointTraceIdentities2156a.exit', 'SourceGammaOnePrimitiveJointTraceIdentities2156a.lean.txt', 'SourceGammaOnePrimitiveJointTraceIdentities2156a.log', 'SourceGammaOnePrimitiveJointTraceIdentities2156b.exit', 'SourceGammaOnePrimitiveJointTraceIdentities2156b.lean.txt', 'SourceGammaOnePrimitiveJointTraceIdentities2156b.log', 'SourceGammaOnePrimitiveJointTraceIdentities2156c.exit', 'SourceGammaOnePrimitiveJointTraceIdentities2156c.lean', 'SourceGammaOnePrimitiveJointTraceIdentities2156c.log', 'SourceGammaOnePrimitiveJointTraceRange-2165.exit', 'SourceGammaOnePrimitiveJointTraceRange-2165.log', 'SourceGammaOnePrimitiveJointTraceRange.lean', 'SourceGammaOnePrimitiveJointTraceRange2154a.exit', 'SourceGammaOnePrimitiveJointTraceRange2154a.lean', 'SourceGammaOnePrimitiveJointTraceRange2154a.log', 'SourceGammaOnePrimitiveJointTraceSpecialization-2165.exit', 'SourceGammaOnePrimitiveJointTraceSpecialization-2165.log', 'SourceGammaOnePrimitiveJointTraceSpecialization.lean', 'SourceGammaOnePrimitiveJointTraceSpecialization2158a.exit', 'SourceGammaOnePrimitiveJointTraceSpecialization2158a.lean.txt', 'SourceGammaOnePrimitiveJointTraceSpecialization2158a.log', 'SourceGammaOnePrimitiveJointTraceSpecialization2158b.exit', 'SourceGammaOnePrimitiveJointTraceSpecialization2158b.lean', 'SourceGammaOnePrimitiveJointTraceSpecialization2158b.log', 'SourceGammaOnePrimitiveJointTraceSpecializedFrobenius-2165.exit', 'SourceGammaOnePrimitiveJointTraceSpecializedFrobenius-2165.log', 'SourceGammaOnePrimitiveJointTraceSpecializedFrobenius.lean', 'SourceGammaOnePrimitiveJointTraceSpecializedFrobenius2159a.exit', 'SourceGammaOnePrimitiveJointTraceSpecializedFrobenius2159a.lean.txt', 'SourceGammaOnePrimitiveJointTraceSpecializedFrobenius2159a.log', 'SourceGammaOnePrimitiveJointTraceSpecializedFrobenius2159b.exit', 'SourceGammaOnePrimitiveJointTraceSpecializedFrobenius2159b.lean', 'SourceGammaOnePrimitiveJointTraceSpecializedFrobenius2159b.log', 'SourceGammaOnePrimitiveJointUnitDiamond-2165.exit', 'SourceGammaOnePrimitiveJointUnitDiamond-2165.log', 'SourceGammaOnePrimitiveJointUnitDiamond.lean', 'SourceGammaOnePrimitiveJointUnitDiamond2145a.exit', 'SourceGammaOnePrimitiveJointUnitDiamond2145a.lean', 'SourceGammaOnePrimitiveJointUnitDiamond2145a.log', 'SourceGammaOnePrimitiveTraceAudit1.exit', 'SourceGammaOnePrimitiveTraceAudit1.lean', 'SourceGammaOnePrimitiveTraceAudit1.log', 'SourceGammaOnePrimitiveTraceDependencyAudit1.exit', 'SourceGammaOnePrimitiveTraceDependencyAudit1.lean', 'SourceGammaOnePrimitiveTraceDependencyAudit1.log', 'SourceGammaOnePrimitiveTraceScratchOwnership2165.exit', 'SourceGammaOnePrimitiveTraceScratchOwnership2165.lean', 'SourceGammaOnePrimitiveTraceScratchOwnership2165.log', 'SourceGammaOnePrimitiveUnitDiamond-2165.exit', 'SourceGammaOnePrimitiveUnitDiamond-2165.log', 'SourceGammaOnePrimitiveUnitDiamond.lean', 'SourceGammaOnePrimitiveUnitDiamond2144a.exit', 'SourceGammaOnePrimitiveUnitDiamond2144a.lean', 'SourceGammaOnePrimitiveUnitDiamond2144a.log', 'SourceGroupAlgebraTrace-2190.exit', 'SourceGroupAlgebraTrace-2190.log', 'SourceGroupAlgebraTrace.lean', 'SourceGroupAlgebraTrace2179a.exit', 'SourceGroupAlgebraTrace2179a.lean.txt', 'SourceGroupAlgebraTrace2179a.log', 'SourceGroupAlgebraTrace2179b.exit', 'SourceGroupAlgebraTrace2179b.lean', 'SourceGroupAlgebraTrace2179b.log', 'SourceGroupTraceTrilinear-2190.exit', 'SourceGroupTraceTrilinear-2190.log', 'SourceGroupTraceTrilinear.lean', 'SourceGroupTraceTrilinear2180a.exit', 'SourceGroupTraceTrilinear2180a.lean.txt', 'SourceGroupTraceTrilinear2180a.log', 'SourceGroupTraceTrilinear2180b.exit', 'SourceGroupTraceTrilinear2180b.lean', 'SourceGroupTraceTrilinear2180b.log', 'SourceOriginalLocalTraceAudit1.exit', 'SourceOriginalLocalTraceAudit1.lean', 'SourceOriginalLocalTraceAudit1.log', 'SourceOriginalLocalTraceDependencyAudit1.exit', 'SourceOriginalLocalTraceDependencyAudit1.lean', 'SourceOriginalLocalTraceDependencyAudit1.log', 'SourceOriginalLocalTraceScratchOwnership2176.exit', 'SourceOriginalLocalTraceScratchOwnership2176.lean', 'SourceOriginalLocalTraceScratchOwnership2176.log', 'SourceOriginalTraceAlgebraAudit1.exit', 'SourceOriginalTraceAlgebraAudit1.lean.txt', 'SourceOriginalTraceAlgebraAudit1.log', 'SourceOriginalTraceAlgebraAudit2.exit', 'SourceOriginalTraceAlgebraAudit2.lean', 'SourceOriginalTraceAlgebraAudit2.log', 'SourceOriginalTraceAlgebraDependencyAudit1.lean.txt', 'SourceOriginalTraceAlgebraDependencyAudit2.exit', 'SourceOriginalTraceAlgebraDependencyAudit2.lean', 'SourceOriginalTraceAlgebraDependencyAudit2.lean.txt', 'SourceOriginalTraceAlgebraDependencyAudit2.log', 'SourceOriginalTraceAlgebraDependencyAudit3.exit', 'SourceOriginalTraceAlgebraDependencyAudit3.lean', 'SourceOriginalTraceAlgebraDependencyAudit3.log', 'SourceOriginalTraceAlgebraScratchOwnership2190.exit', 'SourceOriginalTraceAlgebraScratchOwnership2190.lean', 'SourceOriginalTraceAlgebraScratchOwnership2190.log', 'SourcePositiveAdicFamilyLift-2176.exit', 'SourcePositiveAdicFamilyLift-2176.log', 'SourcePositiveAdicFamilyLift.lean', 'SourcePositiveAdicFamilyLift2167a.exit', 'SourcePositiveAdicFamilyLift2167a.lean.txt', 'SourcePositiveAdicFamilyLift2167a.log', 'SourcePositiveAdicFamilyLift2167b.exit', 'SourcePositiveAdicFamilyLift2167b.lean', 'SourcePositiveAdicFamilyLift2167b.log', 'SourcePositiveAdicReconstruction-2176.exit', 'SourcePositiveAdicReconstruction-2176.log', 'SourcePositiveAdicReconstruction.lean', 'SourcePositiveAdicReconstruction2168a.exit', 'SourcePositiveAdicReconstruction2168a.lean', 'SourcePositiveAdicReconstruction2168a.log', 'SourceTraceDeterminantTrilinear-2190.exit', 'SourceTraceDeterminantTrilinear-2190.log', 'SourceTraceDeterminantTrilinear.lean', 'SourceTraceDeterminantTrilinear2178a.exit', 'SourceTraceDeterminantTrilinear2178a.lean.txt', 'SourceTraceDeterminantTrilinear2178a.log', 'SourceTraceDeterminantTrilinear2178b.exit', 'SourceTraceDeterminantTrilinear2178b.lean', 'SourceTraceDeterminantTrilinear2178b.log', 'SourceTraceIdempotentCorner-2190.exit', 'SourceTraceIdempotentCorner-2190.log', 'SourceTraceIdempotentCorner.lean', 'SourceTraceIdempotentCorner2186a.exit', 'SourceTraceIdempotentCorner2186a.lean.txt', 'SourceTraceIdempotentCorner2186a.log', 'SourceTraceIdempotentCorner2186b.exit', 'SourceTraceIdempotentCorner2186b.lean', 'SourceTraceIdempotentCorner2186b.log', 'SourceTraceQuotientQuadratic-2190.exit', 'SourceTraceQuotientQuadratic-2190.log', 'SourceTraceQuotientQuadratic.lean', 'SourceTraceQuotientQuadratic2185a.exit', 'SourceTraceQuotientQuadratic2185a.lean', 'SourceTraceQuotientQuadratic2185a.log', 'SourceTraceRadical-2190.exit', 'SourceTraceRadical-2190.log', 'SourceTraceRadical.lean', 'SourceTraceRadical2182a.exit', 'SourceTraceRadical2182a.lean.txt', 'SourceTraceRadical2182a.log', 'SourceTraceRadical2182b.exit', 'SourceTraceRadical2182b.lean', 'SourceTraceRadical2182b.log', 'SourceTraceRadicalQuotient-2190.exit', 'SourceTraceRadicalQuotient-2190.log', 'SourceTraceRadicalQuotient.lean', 'SourceTraceRadicalQuotient2184a.exit', 'SourceTraceRadicalQuotient2184a.lean', 'SourceTraceRadicalQuotient2184a.log', 'SourceUnitTraceConjugation-2165.exit', 'SourceUnitTraceConjugation-2165.log', 'SourceUnitTraceConjugation.lean', 'SourceUnitTraceConjugation2152a.exit', 'SourceUnitTraceConjugation2152a.lean', 'SourceUnitTraceConjugation2152a.log', 'SourceUnitTraceProduct-2165.exit', 'SourceUnitTraceProduct-2165.log', 'SourceUnitTraceProduct.lean', 'SourceUnitTraceProduct2155a.exit', 'SourceUnitTraceProduct2155a.lean', 'SourceUnitTraceProduct2155a.log', 'characteristic-zero-reconstruction-reuse-2169.json', 'original-local-trace-audit-config-2176.json', 'original-local-trace-promotion-route-2183.json', 'original-local-trace-route-2175.json', 'original-trace-algebra-audit-config-2190.json', 'original-trace-algebra-audit-config-2190b.json', 'original-trace-algebra-audit-config-2190c.json', 'original-trace-algebra-promotion-route-2204.json', 'original-trace-algebra-registration-correction-2190b.json', 'original-trace-algebra-route-2189.json', 'prepare_original_local_trace_audit_2176.py', 'prepare_original_trace_algebra_audit_2190.py', 'prepare_primitive_trace_audit_2165.py', 'primitive-joint-trace-route-2161.json', 'primitive-trace-audit-config-2165.json', 'rank-two-trace-realization-route-2177.json', 'record_original_local_trace_audit_2181.py', 'record_original_trace_algebra_audit_2193c.py', 'record_primitive_trace_audit_2174.py', 'run_original_trace_algebra_dependency_audit_2190c.ps1', 'run_original_trace_algebra_successor_audit_2190b.ps1', 'source-gammaone-primitive-trace-1-reuse-review-20261116.json', 'source-gammaone-primitive-trace-1-scratch-receipt.json', 'source-original-local-trace-1-reuse-review-20261116.json', 'source-original-local-trace-1-scratch-receipt.json', 'source-original-trace-algebra-1-reuse-review-20261116.json', 'source-original-trace-algebra-1-scratch-receipt.json']]
for cert in certs:
    evidence.append(Path(cert['reuseReview']))

for cert in certs:
    for field in ['log','dependencyAuditLog']:
        f=Path(cert[field]); evidence.extend([f,f.with_suffix('.lean'),f.with_suffix('.exit')])
archive=[]
archiveBytes={}
for source in dict.fromkeys(evidence):
    assert source.exists(),source
    target=r/archive_rel/source.relative_to(p)
    if source.suffix in ['.lean','.md']:target=target.with_name(target.name+'.txt')
    assert not target.exists(),target
    data=source.read_bytes()
    if target in archiveBytes and archiveBytes[target]!=data:
        target=target.with_name(target.name+'.source-'+sha(source)[:16]+'.txt')
        assert not target.exists(),target
    if target in archiveBytes:assert archiveBytes[target]==data,target
    else:
        archiveBytes[target]=data
        refresh_pending.append((target,data,'Tools'))
    archive.append(dict(source=str(source),path=target.relative_to(r).as_posix(),sha256=sha(source)))
archive_target=r/archive_rel/'archive-manifest.json'
assert not archive_target.exists()
refresh_pending.append((archive_target,(json.dumps(dict(files=archive),indent=2)+'\n').encode(),'Tools'))
supplemental_review_path=r/archive_rel/'original-trace-algebra-promotion-route-2204.json'

audit = r / "Extension/Dubon2026/Audit.lean"
at = audit.read_text(encoding="utf-8")
for n in queries:
    assert not re.search(r"``" + re.escape(n) + r"(?=[,\s])", at)
tm, dm = "\n]\n\nprivate def publicConstructions", "\n]\n\nprivate def runAudit"
assert at.count(tm) == at.count(dm) == 1
at = at.replace(tm, "".join("\n  ,``" + n for n in theorems) + tm, 1)
at = at.replace(dm, "".join("\n  ," + chr(96)*2 + n for n in defs) + dm, 1)
research_path = r / "Tools/lean-reuse-audit-20261020.json"
reuse_path = r / "Tools/source-original-trace-algebra.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt9611"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> automorphy -> original all-weight characteristic-zero association -> actual rank-two realization of the original continuous characteristic-zero trace -> compatible original adic traces. -> actual group-algebra trace radical quotient.'
discharged = 'The actual primitive joint action and cyclotomic determinant yield traces in the original Hecke image by native finite-factor Chebotarev and actual norm-Frobenius comparison. Specialization by the original Fourier character gives continuous trace/determinant pairs at every positive adic precision. Native Krull neighborhoods and Frobenius equality prove compatibility under every original quotient transition. Native adic completion reconstructs their unique values and all trace identities in the actual complete coefficient ring. The existing compact separated local ring theorem proves its original topology is adic. The original modular form supplies the genuine finite local coefficient extension, valuation extension, embedding and residue characteristic, giving continuous characteristic-zero traces with exact original Fourier and weight determinant values at every good-prime norm Frobenius. Compatibility, trace image membership, reconstruction, coefficient completeness and topology are derived; none is an independent source-consumer premise. The prime range remains p greater than three. The original continuous field-valued traces then construct an actual algebra and group action in its units. Native group-algebra induction extends the trace identities; quotienting by the actual two-sided trace radical derives a nondegenerate trace pairing, the polarized quadratic identity and scalar trace-one idempotent corners. No trace algebra, pairing nondegeneracy or group action is supplied as an independent source-consumer premise.'
boundary = 'Actual rank-two matrix realization, primes two and three, full original all-weight association, remaining local/image/regularity inputs, automorphy and literal higher symmetric-power continuation remain required. A continuous trace satisfying the dimension-two identities is not yet a matrix representation. Acceptance stays 16/20; DUB-17--20 OPEN; all source and verification criteria are unchanged. The constructed algebra is not yet a continuous two-dimensional matrix representation; group-image spanning and actual matrix continuity still need their explicit bridges.'
status = 'The 34-module scratch scope passes 76 public axiom queries, 206 exhaustive theorem checks, sixteen linters per module and three declaration-value audits with 83 required dependencies, with zero diagnostics. Production aggregate, focused audits and sequential foundation/paper verification of the 9,645-module scope are pending.'
route = 'The expanded pinned public-source review and targeted pseudocharacter follow-up preceded this route. Reuse the actual original joint Hecke character, native Chebotarev, original norm Frobenius, native Krull neighborhood basis, quotient transitions and AdicCompletion.ofAlgEquiv. Reuse compactSeparatedLocalRing_isAdic and native local-field completeness instead of developing a new valuation topology. Reuse the original finite common coefficient field and residue-characteristic bridge. The local trace consumer explicitly retains the constructed uniform topology rather than an inherited algebraic-closure subtype topology. Nineteen compatible-trace modules and six reconstruction modules have separate exhaustive scratch audits and strict proof-VALUE checks. The local Frobenius existential helper is separately axiom checked; the final original consumer uses the universal norm-Frobenius theorem. Failed variants and one interrupted large elaboration remain archived; a generic comparison lemma resolves that elaboration without raised limits. All promoted mathematical bodies are unchanged; only imports are qualified. The frozen source, pins and owner-only BAT are unchanged. The trace-algebra scope additionally reuses native MonoidAlgebra, Submodule.liftQ, ideal quotients and MonoidHom.toHomUnits. Its Prop-valued two-sidedness instance is registered as a theorem according to Lean declaration kind. The definitional quotient-mk lemma is separately axiom checked, not claimed as a proof-VALUE edge. The strict VALUE audit traverses the exact upstream scratch modules, with all failed audit evidence preserved. The combined 34-module scope has three independent audits and 83 required VALUE dependencies.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Original characteristic-zero trace algebra (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 9,611-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
corrections = []
count = sum(z['exhaustiveTheorems'] for z in certs)
assert count == 206

docpaths = list(dict.fromkeys(r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]))
for f in docpaths:
    assert "\n\n" in f.read_text(encoding="utf-8")
readmes = [(r.parent / "README.md", "Current Project 83 status ("), (repo / "README.md", "Project 83 has an ")]
for f, prefix in readmes:
    assert sum(line.startswith(prefix) for line in f.read_text(encoding="utf-8").splitlines()) == 1
arch = r / "Dubon Architecture.md"
edge = '  ARITH9611["Original character on explicit primitive joint arithmetic system proved: norm inertia, Frobenius and commutativity discharged. Compatible specialization, rank-two association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourceOriginalTraceAlgebraProductionAudit9645.lean',p/'source-original-trace-algebra-9645-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production9645.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/primitive-joint-arithmetic-20261116-2149'
registered = {row['path'] for row in c['files']}
for priorFile in priorArchive.iterdir():
    rel = priorFile.relative_to(r).as_posix()
    if priorFile.is_file() and rel not in registered:
        c['files'].append({'path': rel, 'role': 'Tools'})

reportSource = p / 'Dubon Original Trace Algebra Assessment 2026-11-16.md'
assert sha(reportSource) == '61A56B3702C1E9B26EC0C3E68D08DCE29D902EA357C69287E8E41F83667E8737'
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
    "productionModules": 9645, "modules": newmods, "queries": queries,
    "theoremRegistrations": theorems, "constructionRegistrations": defs,
    "sourceHashes": {mapping[t.stem]: sha(t) for t, _ in pending}, "scratchCertificates": certs,
    "exactDependency": dependency, "assumptionsDischarged": discharged, "stillOpen": boundary,
    "status": status, "rootPinsChanged": False, "proofLimitsChanged": False,
    "promotionChanges": 'Only canonical and versioned scratch imports are qualified to their registered production modules. All audited statements, proof bodies and comments remain identical. Original function fields and actual modular forms are retained; no assumption or completion criterion is weakened.',
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
arch.write_text(arch.read_text(encoding='utf-8').replace(edge,'  ARITH9611["Original finite primitive joint arithmetic system and exact image commutativity proved (DUB-17/18)"] --> TRACEALG9645\n  TRACEALG9645["Original continuous characteristic-zero traces and faithful trace algebra constructed. Rank-two matrices, continuity, association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'),encoding='utf-8')



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Original characteristic-zero trace algebra - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-original-trace-algebra.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub('  logInfo m!".*"\n', '  logInfo m!"SOURCE ORIGINAL TRACE ALGEBRA AUDIT PASS: {count} theorems including private/generated declarations. Original characteristic-zero trace algebra with exact Fourier Frobenius values proved. Rank-two realization and source gates OPEN;16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourceOriginalTraceAlgebraProductionAudit9645.lean").write_text(out, encoding="utf-8")
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
    target = p / (source.stem + "Production9645.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
(p / "source-original-trace-algebra-9645-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 9645, "increment": 34, "queries": 76,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
