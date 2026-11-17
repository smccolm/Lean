from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 9568
assert d["appliedSourceExactJointCharacter"]["receipt9568"]["exit"] == 0
assert (p / "paper-verification-9568-console.exit").read_text().strip() == "0"
assert (r/'Tools/exact-joint-character-20261116-2096/canonical-evidence-9568.json').exists()
key = "appliedSourcePrimitiveJointArithmetic"
assert key not in d
digests = {'source-gammaone-primitive-column-1-scratch-receipt.json': 'BF7E2E30BC1AF90ECBCB939A48CA0C6796E11DB4F916BF5128D1829EAE822816', 'source-gammaone-primitive-arithmetic-1-scratch-receipt.json': '59445EE93CA79E90ECD30A97B210DFD4B78155BDA4DE2D4D68E419C7DD33B65C'}

for name, digest in digests.items():
    assert sha(p / name) == digest
certs = [json.loads((p / name).read_text(encoding="utf-8")) for name in digests]
mods = [m for z in certs for m in z["modules"]]
queries = [q for z in certs for q in z["queries"]]
theorems = [q for z in certs for q in z["theoremRegistrations"]]
defs = [q for z in certs for q in z["constructionRegistrations"]]
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (43, 43, 107, 87, 20)
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
archive_rel='Tools/primitive-joint-arithmetic-20261116-2149'
evidence=[p/n for n in ['Dubon Primitive Joint Arithmetic Assessment 2026-11-16.md', 'SourceGammaOneFiniteBinaryBoundary-2050-retained.lean.txt', 'SourceGammaOneFiniteBinaryBoundary-2050.exit', 'SourceGammaOneFiniteBinaryBoundary-2050.log', 'SourceGammaOneFiniteBinaryBoundary-2055.exit', 'SourceGammaOneFiniteBinaryBoundary-2055.log', 'SourceGammaOneFiniteBinaryBoundary-2118.exit', 'SourceGammaOneFiniteBinaryBoundary-2118.log', 'SourceGammaOneFiniteBinaryBoundary.lean', 'SourceGammaOneFiniteBinaryBoundary2048a.exit', 'SourceGammaOneFiniteBinaryBoundary2048a.lean.txt', 'SourceGammaOneFiniteBinaryBoundary2048a.log', 'SourceGammaOneFiniteBinaryBoundary2048b.exit', 'SourceGammaOneFiniteBinaryBoundary2048b.lean.txt', 'SourceGammaOneFiniteBinaryBoundary2048b.log', 'SourceGammaOneFiniteBinaryBoundary2048c.exit', 'SourceGammaOneFiniteBinaryBoundary2048c.lean', 'SourceGammaOneFiniteBinaryBoundary2048c.log', 'SourceGammaOneGeometricPrimitiveJointCharacter-2140.exit', 'SourceGammaOneGeometricPrimitiveJointCharacter-2140.log', 'SourceGammaOneGeometricPrimitiveJointCharacter.lean', 'SourceGammaOneGeometricPrimitiveJointCharacter2129a.exit', 'SourceGammaOneGeometricPrimitiveJointCharacter2129a.lean', 'SourceGammaOneGeometricPrimitiveJointCharacter2129a.log', 'SourceGammaOnePrimeHeckeCardinality-2118.exit', 'SourceGammaOnePrimeHeckeCardinality-2118.log', 'SourceGammaOnePrimeHeckeCardinality.lean', 'SourceGammaOnePrimeHeckeCardinality2099a.exit', 'SourceGammaOnePrimeHeckeCardinality2099a.lean.txt', 'SourceGammaOnePrimeHeckeCardinality2099a.log', 'SourceGammaOnePrimeHeckeCardinality2099b.exit', 'SourceGammaOnePrimeHeckeCardinality2099b.lean', 'SourceGammaOnePrimeHeckeCardinality2099b.log', 'SourceGammaOnePrimitiveArithmeticAudit1.exit', 'SourceGammaOnePrimitiveArithmeticAudit1.lean', 'SourceGammaOnePrimitiveArithmeticAudit1.log', 'SourceGammaOnePrimitiveArithmeticDependencyAudit1.exit', 'SourceGammaOnePrimitiveArithmeticDependencyAudit1.lean', 'SourceGammaOnePrimitiveArithmeticDependencyAudit1.log', 'SourceGammaOnePrimitiveArithmeticScratchOwnership2143.exit', 'SourceGammaOnePrimitiveArithmeticScratchOwnership2143.lean', 'SourceGammaOnePrimitiveArithmeticScratchOwnership2143.log', 'SourceGammaOnePrimitiveBoundaryDescent-2140.exit', 'SourceGammaOnePrimitiveBoundaryDescent-2140.log', 'SourceGammaOnePrimitiveBoundaryDescent.lean', 'SourceGammaOnePrimitiveBoundaryDescent2123a.exit', 'SourceGammaOnePrimitiveBoundaryDescent2123a.lean', 'SourceGammaOnePrimitiveBoundaryDescent2123a.log', 'SourceGammaOnePrimitiveBoundaryGalois-2140.exit', 'SourceGammaOnePrimitiveBoundaryGalois-2140.log', 'SourceGammaOnePrimitiveBoundaryGalois.lean', 'SourceGammaOnePrimitiveBoundaryGalois2122a.exit', 'SourceGammaOnePrimitiveBoundaryGalois2122a.lean.txt', 'SourceGammaOnePrimitiveBoundaryGalois2122a.log', 'SourceGammaOnePrimitiveBoundaryGalois2122b.exit', 'SourceGammaOnePrimitiveBoundaryGalois2122b.lean', 'SourceGammaOnePrimitiveBoundaryGalois2122b.log', 'SourceGammaOnePrimitiveBoundaryGaloisWords-2140.exit', 'SourceGammaOnePrimitiveBoundaryGaloisWords-2140.log', 'SourceGammaOnePrimitiveBoundaryGaloisWords.lean', 'SourceGammaOnePrimitiveBoundaryGaloisWords2130a.exit', 'SourceGammaOnePrimitiveBoundaryGaloisWords2130a.lean', 'SourceGammaOnePrimitiveBoundaryGaloisWords2130a.log', 'SourceGammaOnePrimitiveBoundaryOperatorCommute-2140.exit', 'SourceGammaOnePrimitiveBoundaryOperatorCommute-2140.log', 'SourceGammaOnePrimitiveBoundaryOperatorCommute.lean', 'SourceGammaOnePrimitiveBoundaryOperatorCommute2136a.exit', 'SourceGammaOnePrimitiveBoundaryOperatorCommute2136a.lean', 'SourceGammaOnePrimitiveBoundaryOperatorCommute2136a.log', 'SourceGammaOnePrimitiveBoundaryOrbit-2055.exit', 'SourceGammaOnePrimitiveBoundaryOrbit-2055.log', 'SourceGammaOnePrimitiveBoundaryOrbit-2118.exit', 'SourceGammaOnePrimitiveBoundaryOrbit-2118.log', 'SourceGammaOnePrimitiveBoundaryOrbit.lean', 'SourceGammaOnePrimitiveBoundaryOrbit2051a.exit', 'SourceGammaOnePrimitiveBoundaryOrbit2051a.lean', 'SourceGammaOnePrimitiveBoundaryOrbit2051a.log', 'SourceGammaOnePrimitiveBoundaryQuadratic-2140.exit', 'SourceGammaOnePrimitiveBoundaryQuadratic-2140.log', 'SourceGammaOnePrimitiveBoundaryQuadratic.lean', 'SourceGammaOnePrimitiveBoundaryQuadratic2121a.exit', 'SourceGammaOnePrimitiveBoundaryQuadratic2121a.lean', 'SourceGammaOnePrimitiveBoundaryQuadratic2121a.log', 'SourceGammaOnePrimitiveBoundaryWords2124a.exit', 'SourceGammaOnePrimitiveBoundaryWords2124a.lean', 'SourceGammaOnePrimitiveBoundaryWords2124a.log', 'SourceGammaOnePrimitiveColumnAudit1.exit', 'SourceGammaOnePrimitiveColumnAudit1.lean', 'SourceGammaOnePrimitiveColumnAudit1.log', 'SourceGammaOnePrimitiveColumnBoundary-2118.exit', 'SourceGammaOnePrimitiveColumnBoundary-2118.log', 'SourceGammaOnePrimitiveColumnBoundary.lean', 'SourceGammaOnePrimitiveColumnBoundary2106a.exit', 'SourceGammaOnePrimitiveColumnBoundary2106a.lean', 'SourceGammaOnePrimitiveColumnBoundary2106a.log', 'SourceGammaOnePrimitiveColumnDependencyAudit1.exit', 'SourceGammaOnePrimitiveColumnDependencyAudit1.lean.txt', 'SourceGammaOnePrimitiveColumnDependencyAudit1.log', 'SourceGammaOnePrimitiveColumnDependencyAudit2.exit', 'SourceGammaOnePrimitiveColumnDependencyAudit2.lean', 'SourceGammaOnePrimitiveColumnDependencyAudit2.log', 'SourceGammaOnePrimitiveColumnDiamond-2118.exit', 'SourceGammaOnePrimitiveColumnDiamond-2118.log', 'SourceGammaOnePrimitiveColumnDiamond.lean', 'SourceGammaOnePrimitiveColumnDiamond2117a.exit', 'SourceGammaOnePrimitiveColumnDiamond2117a.lean.txt', 'SourceGammaOnePrimitiveColumnDiamond2117a.log', 'SourceGammaOnePrimitiveColumnDiamond2117b.exit', 'SourceGammaOnePrimitiveColumnDiamond2117b.lean', 'SourceGammaOnePrimitiveColumnDiamond2117b.log', 'SourceGammaOnePrimitiveColumnHecke-2118.exit', 'SourceGammaOnePrimitiveColumnHecke-2118.log', 'SourceGammaOnePrimitiveColumnHecke.lean', 'SourceGammaOnePrimitiveColumnHecke2115a.exit', 'SourceGammaOnePrimitiveColumnHecke2115a.lean.txt', 'SourceGammaOnePrimitiveColumnHecke2115a.log', 'SourceGammaOnePrimitiveColumnHecke2115b.exit', 'SourceGammaOnePrimitiveColumnHecke2115b.lean.txt', 'SourceGammaOnePrimitiveColumnHecke2115b.log', 'SourceGammaOnePrimitiveColumnHecke2115c.exit', 'SourceGammaOnePrimitiveColumnHecke2115c.lean', 'SourceGammaOnePrimitiveColumnHecke2115c.log', 'SourceGammaOnePrimitiveColumnScratchOwnership2118.exit', 'SourceGammaOnePrimitiveColumnScratchOwnership2118.lean', 'SourceGammaOnePrimitiveColumnScratchOwnership2118.log', 'SourceGammaOnePrimitiveCuspBoundary-2050-retained.lean.txt', 'SourceGammaOnePrimitiveCuspBoundary-2050.exit', 'SourceGammaOnePrimitiveCuspBoundary-2050.log', 'SourceGammaOnePrimitiveCuspBoundary-2055.exit', 'SourceGammaOnePrimitiveCuspBoundary-2055.log', 'SourceGammaOnePrimitiveCuspBoundary-2118.exit', 'SourceGammaOnePrimitiveCuspBoundary-2118.log', 'SourceGammaOnePrimitiveCuspBoundary.lean', 'SourceGammaOnePrimitiveCuspBoundary2047a.exit', 'SourceGammaOnePrimitiveCuspBoundary2047a.lean.txt', 'SourceGammaOnePrimitiveCuspBoundary2047a.log', 'SourceGammaOnePrimitiveCuspBoundary2047b.exit', 'SourceGammaOnePrimitiveCuspBoundary2047b.lean.txt', 'SourceGammaOnePrimitiveCuspBoundary2047b.log', 'SourceGammaOnePrimitiveCuspBoundary2047c.exit', 'SourceGammaOnePrimitiveCuspBoundary2047c.lean', 'SourceGammaOnePrimitiveCuspBoundary2047c.log', 'SourceGammaOnePrimitiveCuspBoundary2047d.exit', 'SourceGammaOnePrimitiveCuspBoundary2047d.lean', 'SourceGammaOnePrimitiveCuspBoundary2047d.log', 'SourceGammaOnePrimitiveCuspConjugation-2118.exit', 'SourceGammaOnePrimitiveCuspConjugation-2118.log', 'SourceGammaOnePrimitiveCuspConjugation.lean', 'SourceGammaOnePrimitiveCuspConjugation2107a.exit', 'SourceGammaOnePrimitiveCuspConjugation2107a.lean', 'SourceGammaOnePrimitiveCuspConjugation2107a.log', 'SourceGammaOnePrimitiveCuspValues-2118.exit', 'SourceGammaOnePrimitiveCuspValues-2118.log', 'SourceGammaOnePrimitiveCuspValues.lean', 'SourceGammaOnePrimitiveCuspValues2105a.exit', 'SourceGammaOnePrimitiveCuspValues2105a.lean.txt', 'SourceGammaOnePrimitiveCuspValues2105a.log', 'SourceGammaOnePrimitiveCuspValues2105b.exit', 'SourceGammaOnePrimitiveCuspValues2105b.lean', 'SourceGammaOnePrimitiveCuspValues2105b.log', 'SourceGammaOnePrimitiveDiamond-2118.exit', 'SourceGammaOnePrimitiveDiamond-2118.log', 'SourceGammaOnePrimitiveDiamond.lean', 'SourceGammaOnePrimitiveDiamond2116a.exit', 'SourceGammaOnePrimitiveDiamond2116a.lean.txt', 'SourceGammaOnePrimitiveDiamond2116a.log', 'SourceGammaOnePrimitiveDiamond2116b.exit', 'SourceGammaOnePrimitiveDiamond2116b.lean', 'SourceGammaOnePrimitiveDiamond2116b.log', 'SourceGammaOnePrimitiveDividedTerm-2118.exit', 'SourceGammaOnePrimitiveDividedTerm-2118.log', 'SourceGammaOnePrimitiveDividedTerm.lean', 'SourceGammaOnePrimitiveDividedTerm2108a.exit', 'SourceGammaOnePrimitiveDividedTerm2108a.lean.txt', 'SourceGammaOnePrimitiveDividedTerm2108a.log', 'SourceGammaOnePrimitiveDividedTerm2108b.exit', 'SourceGammaOnePrimitiveDividedTerm2108b.lean', 'SourceGammaOnePrimitiveDividedTerm2108b.log', 'SourceGammaOnePrimitiveFixedCosets-2118.exit', 'SourceGammaOnePrimitiveFixedCosets-2118.log', 'SourceGammaOnePrimitiveFixedCosets.lean', 'SourceGammaOnePrimitiveFixedCosets2101a.exit', 'SourceGammaOnePrimitiveFixedCosets2101a.lean', 'SourceGammaOnePrimitiveFixedCosets2101a.log', 'SourceGammaOnePrimitiveFixedOrbit-2118.exit', 'SourceGammaOnePrimitiveFixedOrbit-2118.log', 'SourceGammaOnePrimitiveFixedOrbit.lean', 'SourceGammaOnePrimitiveFixedOrbit2102a.exit', 'SourceGammaOnePrimitiveFixedOrbit2102a.lean.txt', 'SourceGammaOnePrimitiveFixedOrbit2102a.log', 'SourceGammaOnePrimitiveFixedOrbit2102b.exit', 'SourceGammaOnePrimitiveFixedOrbit2102b.lean', 'SourceGammaOnePrimitiveFixedOrbit2102b.log', 'SourceGammaOnePrimitiveHeckeDiamondWords-2140.exit', 'SourceGammaOnePrimitiveHeckeDiamondWords-2140.log', 'SourceGammaOnePrimitiveHeckeDiamondWords.lean', 'SourceGammaOnePrimitiveHeckeTrace-2118.exit', 'SourceGammaOnePrimitiveHeckeTrace-2118.log', 'SourceGammaOnePrimitiveHeckeTrace.lean', 'SourceGammaOnePrimitiveHeckeTrace2114a.exit', 'SourceGammaOnePrimitiveHeckeTrace2114a.lean.txt', 'SourceGammaOnePrimitiveHeckeTrace2114a.log', 'SourceGammaOnePrimitiveHeckeTrace2114b.exit', 'SourceGammaOnePrimitiveHeckeTrace2114b.lean.txt', 'SourceGammaOnePrimitiveHeckeTrace2114b.log', 'SourceGammaOnePrimitiveHeckeTrace2114c.exit', 'SourceGammaOnePrimitiveHeckeTrace2114c.lean.txt', 'SourceGammaOnePrimitiveHeckeTrace2114c.log', 'SourceGammaOnePrimitiveHeckeTrace2114d.exit', 'SourceGammaOnePrimitiveHeckeTrace2114d.lean', 'SourceGammaOnePrimitiveHeckeTrace2114d.log', 'SourceGammaOnePrimitiveJointArithmeticData-2143.exit', 'SourceGammaOnePrimitiveJointArithmeticData-2143.log', 'SourceGammaOnePrimitiveJointArithmeticData.lean', 'SourceGammaOnePrimitiveJointArithmeticData2142a.exit', 'SourceGammaOnePrimitiveJointArithmeticData2142a.lean.txt', 'SourceGammaOnePrimitiveJointArithmeticData2142a.log', 'SourceGammaOnePrimitiveJointArithmeticData2142b.exit', 'SourceGammaOnePrimitiveJointArithmeticData2142b.lean', 'SourceGammaOnePrimitiveJointArithmeticData2142b.log', 'SourceGammaOnePrimitiveJointArithmeticSystem-2143.exit', 'SourceGammaOnePrimitiveJointArithmeticSystem-2143.log', 'SourceGammaOnePrimitiveJointArithmeticSystem.lean', 'SourceGammaOnePrimitiveJointArithmeticSystem2137a.exit', 'SourceGammaOnePrimitiveJointArithmeticSystem2137a.lean.txt', 'SourceGammaOnePrimitiveJointArithmeticSystem2137a.log', 'SourceGammaOnePrimitiveJointArithmeticSystem2137b.exit', 'SourceGammaOnePrimitiveJointArithmeticSystem2137b.lean.txt', 'SourceGammaOnePrimitiveJointArithmeticSystem2137b.log', 'SourceGammaOnePrimitiveJointArithmeticSystem2137c.exit', 'SourceGammaOnePrimitiveJointArithmeticSystem2137c.lean', 'SourceGammaOnePrimitiveJointArithmeticSystem2137c.log', 'SourceGammaOnePrimitiveJointCharacter-2140.exit', 'SourceGammaOnePrimitiveJointCharacter-2140.log', 'SourceGammaOnePrimitiveJointCharacter.lean', 'SourceGammaOnePrimitiveJointCharacter2127a.lean.txt', 'SourceGammaOnePrimitiveJointCharacter2127b.exit', 'SourceGammaOnePrimitiveJointCharacter2127b.lean', 'SourceGammaOnePrimitiveJointCharacter2127b.log', 'SourceGammaOnePrimitiveJointCharacterValues-2140.exit', 'SourceGammaOnePrimitiveJointCharacterValues-2140.log', 'SourceGammaOnePrimitiveJointCharacterValues.lean', 'SourceGammaOnePrimitiveJointCharacterValues2134a.exit', 'SourceGammaOnePrimitiveJointCharacterValues2134a.lean.txt', 'SourceGammaOnePrimitiveJointCharacterValues2134a.log', 'SourceGammaOnePrimitiveJointCharacterValues2134b.exit', 'SourceGammaOnePrimitiveJointCharacterValues2134b.lean.txt', 'SourceGammaOnePrimitiveJointCharacterValues2134b.log', 'SourceGammaOnePrimitiveJointCharacterValues2134c.exit', 'SourceGammaOnePrimitiveJointCharacterValues2134c.lean', 'SourceGammaOnePrimitiveJointCharacterValues2134c.log', 'SourceGammaOnePrimitiveJointCommutativity-2143.exit', 'SourceGammaOnePrimitiveJointCommutativity-2143.log', 'SourceGammaOnePrimitiveJointCommutativity.lean', 'SourceGammaOnePrimitiveJointCommutativity2139a.exit', 'SourceGammaOnePrimitiveJointCommutativity2139a.lean', 'SourceGammaOnePrimitiveJointCommutativity2139a.log', 'SourceGammaOnePrimitiveJointDescent-2140.exit', 'SourceGammaOnePrimitiveJointDescent-2140.log', 'SourceGammaOnePrimitiveJointDescent.lean', 'SourceGammaOnePrimitiveJointDescent2133a.lean.txt', 'SourceGammaOnePrimitiveJointDescent2133b.exit', 'SourceGammaOnePrimitiveJointDescent2133b.lean.txt', 'SourceGammaOnePrimitiveJointDescent2133b.log', 'SourceGammaOnePrimitiveJointDescent2133c.exit', 'SourceGammaOnePrimitiveJointDescent2133c.lean', 'SourceGammaOnePrimitiveJointDescent2133c.log', 'SourceGammaOnePrimitiveJointFrobenius-2140.exit', 'SourceGammaOnePrimitiveJointFrobenius-2140.log', 'SourceGammaOnePrimitiveJointFrobenius.lean', 'SourceGammaOnePrimitiveJointFrobenius2132a.lean.txt', 'SourceGammaOnePrimitiveJointFrobenius2132b.lean.txt', 'SourceGammaOnePrimitiveJointFrobenius2132c.exit', 'SourceGammaOnePrimitiveJointFrobenius2132c.lean.txt', 'SourceGammaOnePrimitiveJointFrobenius2132c.log', 'SourceGammaOnePrimitiveJointFrobenius2132d.exit', 'SourceGammaOnePrimitiveJointFrobenius2132d.lean.txt', 'SourceGammaOnePrimitiveJointFrobenius2132d.log', 'SourceGammaOnePrimitiveJointFrobenius2132e.exit', 'SourceGammaOnePrimitiveJointFrobenius2132e.lean.txt', 'SourceGammaOnePrimitiveJointFrobenius2132e.log', 'SourceGammaOnePrimitiveJointFrobenius2132f.exit', 'SourceGammaOnePrimitiveJointFrobenius2132f.lean.txt', 'SourceGammaOnePrimitiveJointFrobenius2132f.log', 'SourceGammaOnePrimitiveJointFrobenius2132g.exit', 'SourceGammaOnePrimitiveJointFrobenius2132g.lean.txt', 'SourceGammaOnePrimitiveJointFrobenius2132g.log', 'SourceGammaOnePrimitiveJointFrobenius2132h.exit', 'SourceGammaOnePrimitiveJointFrobenius2132h.lean.txt', 'SourceGammaOnePrimitiveJointFrobenius2132h.log', 'SourceGammaOnePrimitiveJointFrobenius2132i.exit', 'SourceGammaOnePrimitiveJointFrobenius2132i.lean', 'SourceGammaOnePrimitiveJointFrobenius2132i.log', 'SourceGammaOnePrimitiveJointFrobeniusWitness-2143.exit', 'SourceGammaOnePrimitiveJointFrobeniusWitness-2143.log', 'SourceGammaOnePrimitiveJointFrobeniusWitness.lean', 'SourceGammaOnePrimitiveJointFrobeniusWitness2135a.exit', 'SourceGammaOnePrimitiveJointFrobeniusWitness2135a.lean', 'SourceGammaOnePrimitiveJointFrobeniusWitness2135a.log', 'SourceGammaOnePrimitiveJointGalois-2140.exit', 'SourceGammaOnePrimitiveJointGalois-2140.log', 'SourceGammaOnePrimitiveJointGalois.lean', 'SourceGammaOnePrimitiveJointGalois2131a.exit', 'SourceGammaOnePrimitiveJointGalois2131a.lean.txt', 'SourceGammaOnePrimitiveJointGalois2131a.log', 'SourceGammaOnePrimitiveJointGalois2131b.exit', 'SourceGammaOnePrimitiveJointGalois2131b.lean.txt', 'SourceGammaOnePrimitiveJointGalois2131b.log', 'SourceGammaOnePrimitiveJointGalois2131c.exit', 'SourceGammaOnePrimitiveJointGalois2131c.lean', 'SourceGammaOnePrimitiveJointGalois2131c.log', 'SourceGammaOnePrimitiveJointRing-2140.exit', 'SourceGammaOnePrimitiveJointRing-2140.log', 'SourceGammaOnePrimitiveJointRing.lean', 'SourceGammaOnePrimitiveJointRing2126a.exit', 'SourceGammaOnePrimitiveJointRing2126a.lean.txt', 'SourceGammaOnePrimitiveJointRing2126a.log', 'SourceGammaOnePrimitiveJointRing2126b.exit', 'SourceGammaOnePrimitiveJointRing2126b.lean', 'SourceGammaOnePrimitiveJointRing2126b.log', 'SourceGammaOnePrimitiveJointSquare-2140.exit', 'SourceGammaOnePrimitiveJointSquare-2140.log', 'SourceGammaOnePrimitiveJointSquare.lean', 'SourceGammaOnePrimitiveJointSquare2125a.exit', 'SourceGammaOnePrimitiveJointSquare2125a.lean.txt', 'SourceGammaOnePrimitiveJointSquare2125a.log', 'SourceGammaOnePrimitiveJointSquare2125b.exit', 'SourceGammaOnePrimitiveJointSquare2125b.lean', 'SourceGammaOnePrimitiveJointSquare2125b.log', 'SourceGammaOnePrimitiveMultipliedTerm-2118.exit', 'SourceGammaOnePrimitiveMultipliedTerm-2118.log', 'SourceGammaOnePrimitiveMultipliedTerm.lean', 'SourceGammaOnePrimitiveMultipliedTerm2110a.exit', 'SourceGammaOnePrimitiveMultipliedTerm2110a.lean', 'SourceGammaOnePrimitiveMultipliedTerm2110a.log', 'SourceGammaOnePrimitiveOrbitRepresentatives-2118.exit', 'SourceGammaOnePrimitiveOrbitRepresentatives-2118.log', 'SourceGammaOnePrimitiveOrbitRepresentatives.lean', 'SourceGammaOnePrimitiveOrbitRepresentatives2111a.exit', 'SourceGammaOnePrimitiveOrbitRepresentatives2111a.lean.txt', 'SourceGammaOnePrimitiveOrbitRepresentatives2111a.log', 'SourceGammaOnePrimitiveOrbitRepresentatives2111b.exit', 'SourceGammaOnePrimitiveOrbitRepresentatives2111b.lean', 'SourceGammaOnePrimitiveOrbitRepresentatives2111b.log', 'SourceGammaOnePrimitivePrimeOrbits-2118.exit', 'SourceGammaOnePrimitivePrimeOrbits-2118.log', 'SourceGammaOnePrimitivePrimeOrbits.lean', 'SourceGammaOnePrimitivePrimeOrbits2098a.exit', 'SourceGammaOnePrimitivePrimeOrbits2098a.lean.txt', 'SourceGammaOnePrimitivePrimeOrbits2098a.log', 'SourceGammaOnePrimitivePrimeOrbits2098b.exit', 'SourceGammaOnePrimitivePrimeOrbits2098b.lean.txt', 'SourceGammaOnePrimitivePrimeOrbits2098b.log', 'SourceGammaOnePrimitivePrimeOrbits2098c.exit', 'SourceGammaOnePrimitivePrimeOrbits2098c.lean', 'SourceGammaOnePrimitivePrimeOrbits2098c.log', 'SourceGammaOnePrimitiveTermColumns-2118.exit', 'SourceGammaOnePrimitiveTermColumns-2118.log', 'SourceGammaOnePrimitiveTermColumns.lean', 'SourceGammaOnePrimitiveTermColumns2113a.exit', 'SourceGammaOnePrimitiveTermColumns2113a.lean.txt', 'SourceGammaOnePrimitiveTermColumns2113a.log', 'SourceGammaOnePrimitiveTermColumns2113b.exit', 'SourceGammaOnePrimitiveTermColumns2113b.lean', 'SourceGammaOnePrimitiveTermColumns2113b.log', 'SourceGammaOnePrimitiveTwoOrbits-2118.exit', 'SourceGammaOnePrimitiveTwoOrbits-2118.log', 'SourceGammaOnePrimitiveTwoOrbits.lean', 'SourceGammaOnePrimitiveTwoOrbits2103a.exit', 'SourceGammaOnePrimitiveTwoOrbits2103a.lean.txt', 'SourceGammaOnePrimitiveTwoOrbits2103a.log', 'SourceGammaOnePrimitiveTwoOrbits2103b.exit', 'SourceGammaOnePrimitiveTwoOrbits2103b.lean', 'SourceGammaOnePrimitiveTwoOrbits2103b.log', 'SourceGammaOnePrimitiveUnitActions-2140.exit', 'SourceGammaOnePrimitiveUnitActions-2140.log', 'SourceGammaOnePrimitiveUnitActions.lean', 'SourceGammaOnePrimitiveUnitActions2119a.exit', 'SourceGammaOnePrimitiveUnitActions2119a.lean.txt', 'SourceGammaOnePrimitiveUnitActions2119a.log', 'SourceGammaOnePrimitiveUnitActions2119b.exit', 'SourceGammaOnePrimitiveUnitActions2119b.lean', 'SourceGammaOnePrimitiveUnitActions2119b.log', 'SourceGammaOnePrimitiveUnitHecke-2140.exit', 'SourceGammaOnePrimitiveUnitHecke-2140.log', 'SourceGammaOnePrimitiveUnitHecke.lean', 'SourceGammaOnePrimitiveUnitHecke2120a.exit', 'SourceGammaOnePrimitiveUnitHecke2120a.lean.txt', 'SourceGammaOnePrimitiveUnitHecke2120a.log', 'SourceGammaOnePrimitiveUnitHecke2120b.exit', 'SourceGammaOnePrimitiveUnitHecke2120b.lean', 'SourceGammaOnePrimitiveUnitHecke2120b.log', 'SourceGammaOnePrimitiveUpperColumns-2118.exit', 'SourceGammaOnePrimitiveUpperColumns-2118.log', 'SourceGammaOnePrimitiveUpperColumns.lean', 'SourceGammaOnePrimitiveUpperColumns2112a.exit', 'SourceGammaOnePrimitiveUpperColumns2112a.lean', 'SourceGammaOnePrimitiveUpperColumns2112a.log', 'SourceGammaOnePrimitiveWidth-2118.exit', 'SourceGammaOnePrimitiveWidth-2118.log', 'SourceGammaOnePrimitiveWidth.lean', 'SourceGammaOnePrimitiveWidth2097a.exit', 'SourceGammaOnePrimitiveWidth2097a.lean.txt', 'SourceGammaOnePrimitiveWidth2097a.log', 'SourceGammaOnePrimitiveWidth2097b.exit', 'SourceGammaOnePrimitiveWidth2097b.lean', 'SourceGammaOnePrimitiveWidth2097b.log', 'SourceGammaOnePrimitiveWidthColumns-2118.exit', 'SourceGammaOnePrimitiveWidthColumns-2118.log', 'SourceGammaOnePrimitiveWidthColumns.lean', 'SourceGammaOnePrimitiveWidthColumns2104a.exit', 'SourceGammaOnePrimitiveWidthColumns2104a.lean.txt', 'SourceGammaOnePrimitiveWidthColumns2104a.log', 'SourceGammaOnePrimitiveWidthColumns2104b.exit', 'SourceGammaOnePrimitiveWidthColumns2104b.lean.txt', 'SourceGammaOnePrimitiveWidthColumns2104b.log', 'SourceGammaOnePrimitiveWidthColumns2104c.exit', 'SourceGammaOnePrimitiveWidthColumns2104c.lean', 'SourceGammaOnePrimitiveWidthColumns2104c.log', 'SourceUnitQuadraticCommutation-2140.exit', 'SourceUnitQuadraticCommutation-2140.log', 'SourceUnitQuadraticCommutation.lean', 'SourceUnitQuadraticCommutation2138a.exit', 'SourceUnitQuadraticCommutation2138a.lean.txt', 'SourceUnitQuadraticCommutation2138a.log', 'SourceUnitQuadraticCommutation2138b.exit', 'SourceUnitQuadraticCommutation2138b.lean', 'SourceUnitQuadraticCommutation2138b.log', 'prepare_primitive_arithmetic_audit_2143.py', 'prepare_primitive_column_audit_2118.py', 'primitive-arithmetic-audit-config-2143.json', 'primitive-arithmetic-core-2140.json', 'primitive-boundary-arithmetic-route-2109.json', 'primitive-column-audit-config-2118.json', 'primitive-column-audit-config-2118b.json', 'primitive-column-audit-route-2128.json', 'primitive-joint-arithmetic-promotion-route-2149.json', 'primitive-joint-arithmetic-route-2141.json', 'record_primitive_arithmetic_audit_2148.py', 'record_primitive_column_audit_2128.py', 'source-gammaone-primitive-arithmetic-1-reuse-review-20261116.json', 'source-gammaone-primitive-arithmetic-1-scratch-receipt.json', 'source-gammaone-primitive-column-1-reuse-review-20261116.json', 'source-gammaone-primitive-column-1-scratch-receipt.json']]
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
supplemental_review_path=r/archive_rel/'primitive-joint-arithmetic-promotion-route-2149.json'

audit = r / "Extension/Dubon2026/Audit.lean"
at = audit.read_text(encoding="utf-8")
for n in queries:
    assert not re.search(r"``" + re.escape(n) + r"(?=[,\s])", at)
tm, dm = "\n]\n\nprivate def publicConstructions", "\n]\n\nprivate def runAudit"
assert at.count(tm) == at.count(dm) == 1
at = at.replace(tm, "".join("\n  ,``" + n for n in theorems) + tm, 1)
at = at.replace(dm, "".join("\n  ," + chr(96)*2 + n for n in defs) + dm, 1)
research_path = r / "Tools/lean-reuse-audit-20261020.json"
reuse_path = r / "Tools/source-primitive-joint-arithmetic.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt9568"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> automorphy -> original all-weight characteristic-zero association -> compatible character or trace specialization of the original finite arithmetic systems.'
discharged = 'Primitive cusp widths, the two actual Hecke coset orbits and integral conjugation give the exact torsion-sensitive boundary formula. The original primitive-column boundary has precisely the native parabolic kernel and intertwines both Hecke and diamond operators. Its finite unit actions and the original cyclotomic character give a continuous arithmetic boundary representation. Together with the actual Tate diamond quotient, this explicit finite joint operator image carries the original Fourier-field character at every requested precision, with whole-word equality and diamond values one. The same joint Galois action commutes with every original word, kills norm inertia outside Q*p and descends to the prescribed arithmetic group. Proved original geometry, original local Frobenius and Gamma0 diamond lifts give its exact Frobenius quadratic with the diamond term retained. That quadratic and invertibility derive commutativity of the exact joint image. No geometric, boundary-action, parabolic-lift, separator, Frobenius-existence or arithmetic-factorization premise remains in the assembled finite system. The prime range remains p greater than three.'
boundary = 'Compatible character or trace specialization, rank-two characteristic-zero realization, primes two and three, original all-weight association, remaining local/image/regularity inputs, automorphy and literal higher symmetric-power continuation remain required. A finite operator character and a Frobenius quadratic do not by themselves construct a rank-two representation. Acceptance stays 16/20; DUB-17--20 OPEN; all source and verification criteria are unchanged.'
status = 'The 43-module scratch scope passes 107 public axiom queries, 334 exhaustive theorem checks, sixteen linters per module and two declaration-value audits with 95 required dependencies, with zero diagnostics. Production aggregate, focused audits and sequential foundation/paper verification of the 9,611-module scope are pending.'
route = 'The expanded pinned public-source review and renewed native-code searches precede the route. Reuse the original full-H1 transfer and square-integrality character descent, original all-level geometry, actual quotient operators, homogeneous Hecke/diamond coefficient-square identity, continuous cyclotomic character, local Frobenius witnesses and unramified arithmetic descent. The explicit primitive-column boundary supplies arithmetic actions while preserving the original character; it is not asserted identical as a carrier to the earlier literal boundary quotient. Derive joint Hecke commutativity from the Frobenius polynomial and already proved Galois commutation instead of rebuilding Gamma1 correspondence composition. The existing faithful character-fiber theorem covers field-valued specialization; it does not settle all adic precisions. A direct central-trace route using native Chebotarev is under assessment and is not claimed proved. Twenty-two boundary modules and twenty-one arithmetic modules have separate exhaustive audits and strict proof-VALUE checks. The standalone boundary arithmetic-descent theorem is separately axiom checked; the joint descent directly consumes boundary norm inertia. Earlier failed variants, normal elaboration timeouts and diagnostics are preserved. Generic product equalities and explicit choice projections avoid large elaboration expansions without changing proof limits. The earlier deferred primitive-boundary word module is preserved; the new prime/diamond scope has the distinct canonical name SourceGammaOnePrimitiveHeckeDiamondWords. Promotion changes imports only. Paper, root pins and owner-only BAT are unchanged.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Original primitive joint arithmetic system (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 9,568-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
corrections = []
count = sum(z['exhaustiveTheorems'] for z in certs)
assert count == 334

docpaths = list(dict.fromkeys(r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]))
for f in docpaths:
    assert "\n\n" in f.read_text(encoding="utf-8")
readmes = [(r.parent / "README.md", "Current Project 83 status ("), (repo / "README.md", "Project 83 has an ")]
for f, prefix in readmes:
    assert sum(line.startswith(prefix) for line in f.read_text(encoding="utf-8").splitlines()) == 1
arch = r / "Dubon Architecture.md"
edge = '  JOINT9568["Original finite character constructed on exact geometric/boundary operator image; lift and separator premises removed. Arithmetic realization, exceptional primes, association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourcePrimitiveJointArithmeticProductionAudit9611.lean',p/'source-primitive-joint-arithmetic-9611-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production9611.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/exact-joint-character-20261116-2096'
registered = {row['path'] for row in c['files']}
for priorFile in priorArchive.iterdir():
    rel = priorFile.relative_to(r).as_posix()
    if priorFile.is_file() and rel not in registered:
        c['files'].append({'path': rel, 'role': 'Tools'})

reportSource = p / 'Dubon Primitive Joint Arithmetic Assessment 2026-11-16.md'
assert sha(reportSource) == '0D813586A3D85E016E19BE38CF9F765C11B33C5494010CA35670109A001D8D02'
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
    "productionModules": 9611, "modules": newmods, "queries": queries,
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
arch.write_text(arch.read_text(encoding='utf-8').replace(edge,'  JOINT9568["Original finite character on the literal geometric/boundary quotient image proved (DUB-17/18)"] --> ARITH9611\n  ARITH9611["Original character on explicit primitive joint arithmetic system proved: norm inertia, Frobenius and commutativity discharged. Compatible specialization, rank-two association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'),encoding='utf-8')



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Original primitive joint arithmetic system - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-primitive-joint-arithmetic.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub('  logInfo m!".*"\n', '  logInfo m!"SOURCE PRIMITIVE JOINT ARITHMETIC AUDIT PASS: {count} theorems including private/generated declarations. Original finite primitive joint arithmetic system and exact image commutativity proved. Compatible specialization and source gates OPEN;16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourcePrimitiveJointArithmeticProductionAudit9611.lean").write_text(out, encoding="utf-8")
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
    target = p / (source.stem + "Production9611.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
(p / "source-primitive-joint-arithmetic-9611-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 9611, "increment": 43, "queries": 107,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
