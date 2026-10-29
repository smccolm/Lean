from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 9450
assert d["appliedSourceToricMarkedPoint"]["receipt9450"]["exit"] == 0
assert (p / "paper-verification-9450-console.exit").read_text().strip() == "0"
assert (r/'Tools/toric-marked-point-20261029-1901/canonical-evidence-9450.json').exists()
key = "appliedSourceOriginalMarkedChart"
assert key not in d
digests = {'source-marked-chart-construction-1-scratch-receipt.json': '4F65BCEBE48BA23C78D7EC99C918B73A2FC98C8CE5AB69DED31A0C2A1613CA0E', 'source-marked-chart-stabilizer-2-scratch-receipt.json': '7EAE85E0CC6DF676908BDAECB217DAD0DC546536673B8ACCFA7E35CF97BB8353', 'source-marked-natural-chart-1-scratch-receipt.json': 'F0552D451B4B6CAD6F3CD16143E68B20C071BF8FD9D2F6D714E2E6053F970983'}

for name, digest in digests.items():
    assert sha(p / name) == digest
certs = [json.loads((p / name).read_text(encoding="utf-8")) for name in digests]
mods = [m for z in certs for m in z["modules"]]
queries = [q for z in certs for q in z["queries"]]
theorems = [q for z in certs for q in z["theoremRegistrations"]]
defs = [q for z in certs for q in z["constructionRegistrations"]]
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (33, 33, 67, 59, 8)
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
archive_rel='Tools/original-marked-chart-20261029-1943'
evidence=[p/n for n in ['Dubon Original Marked Chart Assessment 2026-10-29.md', 'SourceMarkedChartConstructionAudit1.exit', 'SourceMarkedChartConstructionAudit1.lean', 'SourceMarkedChartConstructionAudit1.log', 'SourceMarkedChartConstructionDependencyAudit1.exit', 'SourceMarkedChartConstructionDependencyAudit1.lean', 'SourceMarkedChartConstructionDependencyAudit1.log', 'SourceMarkedChartConstructionScratchOwnership1914.exit', 'SourceMarkedChartConstructionScratchOwnership1914.lean', 'SourceMarkedChartConstructionScratchOwnership1914.log', 'SourceMarkedChartCoordinateEmbedding-1914.exit', 'SourceMarkedChartCoordinateEmbedding-1914.log', 'SourceMarkedChartCoordinateEmbedding.lean', 'SourceMarkedChartCoordinateEmbedding1902a.exit', 'SourceMarkedChartCoordinateEmbedding1902a.lean', 'SourceMarkedChartCoordinateEmbedding1902a.log', 'SourceMarkedChartDescendedPoint-1914.exit', 'SourceMarkedChartDescendedPoint-1914.log', 'SourceMarkedChartDescendedPoint.lean', 'SourceMarkedChartDescendedPoint1910a.exit', 'SourceMarkedChartDescendedPoint1910a.lean.txt', 'SourceMarkedChartDescendedPoint1910a.log', 'SourceMarkedChartDescendedPoint1910b.exit', 'SourceMarkedChartDescendedPoint1910b.lean.txt', 'SourceMarkedChartDescendedPoint1910b.log', 'SourceMarkedChartDescendedPoint1910c.exit', 'SourceMarkedChartDescendedPoint1910c.lean.txt', 'SourceMarkedChartDescendedPoint1910c.log', 'SourceMarkedChartDescendedPoint1910d.exit', 'SourceMarkedChartDescendedPoint1910d.lean.txt', 'SourceMarkedChartDescendedPoint1910d.log', 'SourceMarkedChartDescendedPoint1910e.exit', 'SourceMarkedChartDescendedPoint1910e.lean', 'SourceMarkedChartDescendedPoint1910e.log', 'SourceMarkedChartDiamondNormalization-1933.exit', 'SourceMarkedChartDiamondNormalization-1933.log', 'SourceMarkedChartDiamondNormalization-1934.exit', 'SourceMarkedChartDiamondNormalization-1934.log', 'SourceMarkedChartDiamondNormalization-failed1933.lean.txt', 'SourceMarkedChartDiamondNormalization.lean', 'SourceMarkedChartDiamondNormalization1922a.exit', 'SourceMarkedChartDiamondNormalization1922a.lean', 'SourceMarkedChartDiamondNormalization1922a.log', 'SourceMarkedChartDiamondNormalization1922b.exit', 'SourceMarkedChartDiamondNormalization1922b.lean', 'SourceMarkedChartDiamondNormalization1922b.log', 'SourceMarkedChartEmbeddingBound-1914.exit', 'SourceMarkedChartEmbeddingBound-1914.log', 'SourceMarkedChartEmbeddingBound.lean', 'SourceMarkedChartEmbeddingBound1908a.exit', 'SourceMarkedChartEmbeddingBound1908a.lean', 'SourceMarkedChartEmbeddingBound1908a.log', 'SourceMarkedChartEmbeddingConjugacy-1933.exit', 'SourceMarkedChartEmbeddingConjugacy-1933.log', 'SourceMarkedChartEmbeddingConjugacy-1934.exit', 'SourceMarkedChartEmbeddingConjugacy-1934.log', 'SourceMarkedChartEmbeddingConjugacy-failed1933.lean.txt', 'SourceMarkedChartEmbeddingConjugacy.lean', 'SourceMarkedChartEmbeddingConjugacy1920a.exit', 'SourceMarkedChartEmbeddingConjugacy1920a.lean.txt', 'SourceMarkedChartEmbeddingConjugacy1920a.log', 'SourceMarkedChartEmbeddingConjugacy1920b.exit', 'SourceMarkedChartEmbeddingConjugacy1920b.lean', 'SourceMarkedChartEmbeddingConjugacy1920b.log', 'SourceMarkedChartEqualJTransfer-1914.exit', 'SourceMarkedChartEqualJTransfer-1914.log', 'SourceMarkedChartEqualJTransfer.lean', 'SourceMarkedChartEqualJTransfer1904a.exit', 'SourceMarkedChartEqualJTransfer1904a.lean.txt', 'SourceMarkedChartEqualJTransfer1904a.log', 'SourceMarkedChartEqualJTransfer1904b.exit', 'SourceMarkedChartEqualJTransfer1904b.lean.txt', 'SourceMarkedChartEqualJTransfer1904b.log', 'SourceMarkedChartEqualJTransfer1904c.exit', 'SourceMarkedChartEqualJTransfer1904c.lean', 'SourceMarkedChartEqualJTransfer1904c.log', 'SourceMarkedChartFieldDescent-1914.exit', 'SourceMarkedChartFieldDescent-1914.log', 'SourceMarkedChartFieldDescent.lean', 'SourceMarkedChartFieldDescent1906a.exit', 'SourceMarkedChartFieldDescent1906a.lean.txt', 'SourceMarkedChartFieldDescent1906a.log', 'SourceMarkedChartFieldDescent1906b.exit', 'SourceMarkedChartFieldDescent1906b.lean', 'SourceMarkedChartFieldDescent1906b.log', 'SourceMarkedChartInvariantSeparation-1914.exit', 'SourceMarkedChartInvariantSeparation-1914.log', 'SourceMarkedChartInvariantSeparation.lean', 'SourceMarkedChartInvariantSeparation1905a.exit', 'SourceMarkedChartInvariantSeparation1905a.lean.txt', 'SourceMarkedChartInvariantSeparation1905a.log', 'SourceMarkedChartInvariantSeparation1905b.exit', 'SourceMarkedChartInvariantSeparation1905b.lean', 'SourceMarkedChartInvariantSeparation1905b.log', 'SourceMarkedChartOriginalConstruction-1914.exit', 'SourceMarkedChartOriginalConstruction-1914.log', 'SourceMarkedChartOriginalConstruction.lean', 'SourceMarkedChartOriginalConstruction1911a.exit', 'SourceMarkedChartOriginalConstruction1911a.lean.txt', 'SourceMarkedChartOriginalConstruction1911a.log', 'SourceMarkedChartOriginalConstruction1911b.exit', 'SourceMarkedChartOriginalConstruction1911b.lean.txt', 'SourceMarkedChartOriginalConstruction1911b.log', 'SourceMarkedChartOriginalConstruction1911c.exit', 'SourceMarkedChartOriginalConstruction1911c.lean', 'SourceMarkedChartOriginalConstruction1911c.log', 'SourceMarkedChartOriginalDiamond-1933.exit', 'SourceMarkedChartOriginalDiamond-1933.log', 'SourceMarkedChartOriginalDiamond-1934.exit', 'SourceMarkedChartOriginalDiamond-1934.log', 'SourceMarkedChartOriginalDiamond-failed1933.lean.txt', 'SourceMarkedChartOriginalDiamond.lean', 'SourceMarkedChartOriginalDiamond1923a.exit', 'SourceMarkedChartOriginalDiamond1923a.lean.txt', 'SourceMarkedChartOriginalDiamond1923a.log', 'SourceMarkedChartOriginalDiamond1923b.exit', 'SourceMarkedChartOriginalDiamond1923b.lean', 'SourceMarkedChartOriginalDiamond1923b.log', 'SourceMarkedChartOriginalSignOrbit-1933.exit', 'SourceMarkedChartOriginalSignOrbit-1933.log', 'SourceMarkedChartOriginalSignOrbit-1934.exit', 'SourceMarkedChartOriginalSignOrbit-1934.log', 'SourceMarkedChartOriginalSignOrbit-failed1933.lean.txt', 'SourceMarkedChartOriginalSignOrbit.lean', 'SourceMarkedChartOriginalSignOrbit1928a.exit', 'SourceMarkedChartOriginalSignOrbit1928a.lean', 'SourceMarkedChartOriginalSignOrbit1928a.log', 'SourceMarkedChartOriginalStabilizer-1914.exit', 'SourceMarkedChartOriginalStabilizer-1914.log', 'SourceMarkedChartOriginalStabilizer.lean', 'SourceMarkedChartOriginalStabilizer1913a.exit', 'SourceMarkedChartOriginalStabilizer1913a.lean', 'SourceMarkedChartOriginalStabilizer1913a.log', 'SourceMarkedChartOriginalStabilizerEquality-1933.exit', 'SourceMarkedChartOriginalStabilizerEquality-1933.log', 'SourceMarkedChartOriginalStabilizerEquality-1934.exit', 'SourceMarkedChartOriginalStabilizerEquality-1934.log', 'SourceMarkedChartOriginalStabilizerEquality-failed1933.lean.txt', 'SourceMarkedChartOriginalStabilizerEquality.lean', 'SourceMarkedChartOriginalStabilizerEquality1932a.exit', 'SourceMarkedChartOriginalStabilizerEquality1932a.lean', 'SourceMarkedChartOriginalStabilizerEquality1932a.log', 'SourceMarkedChartOriginalStabilizerEquality1932b.exit', 'SourceMarkedChartOriginalStabilizerEquality1932b.lean', 'SourceMarkedChartOriginalStabilizerEquality1932b.log', 'SourceMarkedChartPointTransport-1933.exit', 'SourceMarkedChartPointTransport-1933.log', 'SourceMarkedChartPointTransport-1934.exit', 'SourceMarkedChartPointTransport-1934.log', 'SourceMarkedChartPointTransport-failed1933.lean.txt', 'SourceMarkedChartPointTransport.lean', 'SourceMarkedChartPointTransport1921a.exit', 'SourceMarkedChartPointTransport1921a.lean', 'SourceMarkedChartPointTransport1921a.log', 'SourceMarkedChartResidueDegree-1914.exit', 'SourceMarkedChartResidueDegree-1914.log', 'SourceMarkedChartResidueDegree.lean', 'SourceMarkedChartResidueDegree1909a.exit', 'SourceMarkedChartResidueDegree1909a.lean.txt', 'SourceMarkedChartResidueDegree1909a.log', 'SourceMarkedChartResidueDegree1909b.exit', 'SourceMarkedChartResidueDegree1909b.lean.txt', 'SourceMarkedChartResidueDegree1909b.log', 'SourceMarkedChartResidueDegree1909c.exit', 'SourceMarkedChartResidueDegree1909c.lean.txt', 'SourceMarkedChartResidueDegree1909c.log', 'SourceMarkedChartResidueDegree1909d.exit', 'SourceMarkedChartResidueDegree1909d.lean', 'SourceMarkedChartResidueDegree1909d.log', 'SourceMarkedChartStabilizerActions-1933.exit', 'SourceMarkedChartStabilizerActions-1933.log', 'SourceMarkedChartStabilizerActions-1934.exit', 'SourceMarkedChartStabilizerActions-1934.log', 'SourceMarkedChartStabilizerActions-failed1933.lean.txt', 'SourceMarkedChartStabilizerActions.lean', 'SourceMarkedChartStabilizerActions1929a.exit', 'SourceMarkedChartStabilizerActions1929a.lean.txt', 'SourceMarkedChartStabilizerActions1929a.log', 'SourceMarkedChartStabilizerActions1929b.exit', 'SourceMarkedChartStabilizerActions1929b.lean.txt', 'SourceMarkedChartStabilizerActions1929b.log', 'SourceMarkedChartStabilizerActions1929c.exit', 'SourceMarkedChartStabilizerActions1929c.lean.txt', 'SourceMarkedChartStabilizerActions1929c.log', 'SourceMarkedChartStabilizerActions1929d.exit', 'SourceMarkedChartStabilizerActions1929d.lean', 'SourceMarkedChartStabilizerActions1929d.log', 'SourceMarkedChartStabilizerActions1929e.exit', 'SourceMarkedChartStabilizerActions1929e.lean', 'SourceMarkedChartStabilizerActions1929e.log', 'SourceMarkedChartStabilizerAudit1.exit', 'SourceMarkedChartStabilizerAudit1.lean.txt', 'SourceMarkedChartStabilizerAudit1.log', 'SourceMarkedChartStabilizerAudit2.exit', 'SourceMarkedChartStabilizerAudit2.lean', 'SourceMarkedChartStabilizerAudit2.log', 'SourceMarkedChartStabilizerDependencyAudit1.lean', 'SourceMarkedChartStabilizerDependencyAudit2.exit', 'SourceMarkedChartStabilizerDependencyAudit2.lean', 'SourceMarkedChartStabilizerDependencyAudit2.log', 'SourceMarkedChartStabilizerEquality-1933.exit', 'SourceMarkedChartStabilizerEquality-1933.log', 'SourceMarkedChartStabilizerEquality-1934.exit', 'SourceMarkedChartStabilizerEquality-1934.log', 'SourceMarkedChartStabilizerEquality-failed1933.lean.txt', 'SourceMarkedChartStabilizerEquality.lean', 'SourceMarkedChartStabilizerEquality1931a.exit', 'SourceMarkedChartStabilizerEquality1931a.lean', 'SourceMarkedChartStabilizerEquality1931a.log', 'SourceMarkedChartStabilizerEquality1931b.exit', 'SourceMarkedChartStabilizerEquality1931b.lean', 'SourceMarkedChartStabilizerEquality1931b.log', 'SourceMarkedChartStabilizerInclusion-1914.exit', 'SourceMarkedChartStabilizerInclusion-1914.log', 'SourceMarkedChartStabilizerInclusion.lean', 'SourceMarkedChartStabilizerInclusion1912a.exit', 'SourceMarkedChartStabilizerInclusion1912a.lean', 'SourceMarkedChartStabilizerInclusion1912a.log', 'SourceMarkedChartStabilizerScratchOwnership1934.exit', 'SourceMarkedChartStabilizerScratchOwnership1934.lean', 'SourceMarkedChartStabilizerScratchOwnership1934.log', 'SourceMarkedChartTorsionDescent-1914.exit', 'SourceMarkedChartTorsionDescent-1914.log', 'SourceMarkedChartTorsionDescent.lean', 'SourceMarkedChartTorsionDescent1907a.exit', 'SourceMarkedChartTorsionDescent1907a.lean.txt', 'SourceMarkedChartTorsionDescent1907a.log', 'SourceMarkedChartTorsionDescent1907b.exit', 'SourceMarkedChartTorsionDescent1907b.lean', 'SourceMarkedChartTorsionDescent1907b.log', 'SourceMarkedChartVariableInvariants-1914.exit', 'SourceMarkedChartVariableInvariants-1914.log', 'SourceMarkedChartVariableInvariants.lean', 'SourceMarkedChartVariableInvariants1903a.exit', 'SourceMarkedChartVariableInvariants1903a.lean.txt', 'SourceMarkedChartVariableInvariants1903a.log', 'SourceMarkedChartVariableInvariants1903b.exit', 'SourceMarkedChartVariableInvariants1903b.lean', 'SourceMarkedChartVariableInvariants1903b.log', 'SourceMarkedCyclicGeneratorConjugacy-1933.exit', 'SourceMarkedCyclicGeneratorConjugacy-1933.log', 'SourceMarkedCyclicGeneratorConjugacy-1934.exit', 'SourceMarkedCyclicGeneratorConjugacy-1934.log', 'SourceMarkedCyclicGeneratorConjugacy-failed1933.lean.txt', 'SourceMarkedCyclicGeneratorConjugacy.lean', 'SourceMarkedCyclicGeneratorConjugacy1925a.exit', 'SourceMarkedCyclicGeneratorConjugacy1925a.lean.txt', 'SourceMarkedCyclicGeneratorConjugacy1925a.log', 'SourceMarkedCyclicGeneratorConjugacy1925b.exit', 'SourceMarkedCyclicGeneratorConjugacy1925b.lean', 'SourceMarkedCyclicGeneratorConjugacy1925b.log', 'SourceMarkedCyclicRootTransitivity-1933.exit', 'SourceMarkedCyclicRootTransitivity-1933.log', 'SourceMarkedCyclicRootTransitivity-1934.exit', 'SourceMarkedCyclicRootTransitivity-1934.log', 'SourceMarkedCyclicRootTransitivity-failed1933.lean.txt', 'SourceMarkedCyclicRootTransitivity.lean', 'SourceMarkedCyclicRootTransitivity1924a.exit', 'SourceMarkedCyclicRootTransitivity1924a.lean.txt', 'SourceMarkedCyclicRootTransitivity1924a.log', 'SourceMarkedCyclicRootTransitivity1924b.exit', 'SourceMarkedCyclicRootTransitivity1924b.lean', 'SourceMarkedCyclicRootTransitivity1924b.log', 'SourceMarkedNaturalChartAudit1.exit', 'SourceMarkedNaturalChartAudit1.lean', 'SourceMarkedNaturalChartAudit1.log', 'SourceMarkedNaturalChartDependencyAudit1.exit', 'SourceMarkedNaturalChartDependencyAudit1.lean', 'SourceMarkedNaturalChartDependencyAudit1.log', 'SourceMarkedNaturalChartScratchOwnership1939.exit', 'SourceMarkedNaturalChartScratchOwnership1939.lean', 'SourceMarkedNaturalChartScratchOwnership1939.log', 'SourceMarkedNaturalSignChart-1939.exit', 'SourceMarkedNaturalSignChart-1939.log', 'SourceMarkedNaturalSignChart.lean', 'SourceMarkedNaturalSignChart1936a.exit', 'SourceMarkedNaturalSignChart1936a.lean', 'SourceMarkedNaturalSignChart1936a.log', 'SourceMarkedOrbitMap-1939.exit', 'SourceMarkedOrbitMap-1939.log', 'SourceMarkedOrbitMap.lean', 'SourceMarkedOrbitMap1935a.exit', 'SourceMarkedOrbitMap1935a.lean', 'SourceMarkedOrbitMap1935a.log', 'SourceMarkedOriginalNaturalChart-1939.exit', 'SourceMarkedOriginalNaturalChart-1939.log', 'SourceMarkedOriginalNaturalChart.lean', 'SourceMarkedOriginalNaturalChart1938a.exit', 'SourceMarkedOriginalNaturalChart1938a.lean.txt', 'SourceMarkedOriginalNaturalChart1938a.log', 'SourceMarkedOriginalNaturalChart1938b.exit', 'SourceMarkedOriginalNaturalChart1938b.lean', 'SourceMarkedOriginalNaturalChart1938b.log', 'SourceMarkedPointSignTransitivity-1933.exit', 'SourceMarkedPointSignTransitivity-1933.log', 'SourceMarkedPointSignTransitivity-1934.exit', 'SourceMarkedPointSignTransitivity-1934.log', 'SourceMarkedPointSignTransitivity-failed1933.lean.txt', 'SourceMarkedPointSignTransitivity.lean', 'SourceMarkedPointSignTransitivity1927a.exit', 'SourceMarkedPointSignTransitivity1927a.lean', 'SourceMarkedPointSignTransitivity1927a.log', 'SourceMarkedSignChartDiamond-1939.exit', 'SourceMarkedSignChartDiamond-1939.log', 'SourceMarkedSignChartDiamond.lean', 'SourceMarkedSignChartDiamond1937a.exit', 'SourceMarkedSignChartDiamond1937a.lean', 'SourceMarkedSignChartDiamond1937a.log', 'SourceMarkedStabilizerIndexComparison-1933.exit', 'SourceMarkedStabilizerIndexComparison-1933.log', 'SourceMarkedStabilizerIndexComparison-1934.exit', 'SourceMarkedStabilizerIndexComparison-1934.log', 'SourceMarkedStabilizerIndexComparison-failed1933.lean.txt', 'SourceMarkedStabilizerIndexComparison.lean', 'SourceMarkedStabilizerIndexComparison1930a.exit', 'SourceMarkedStabilizerIndexComparison1930a.lean.txt', 'SourceMarkedStabilizerIndexComparison1930a.log', 'SourceMarkedStabilizerIndexComparison1930b.exit', 'SourceMarkedStabilizerIndexComparison1930b.lean', 'SourceMarkedStabilizerIndexComparison1930b.log', 'SourceMarkedTorsionActualCount-1933.exit', 'SourceMarkedTorsionActualCount-1933.log', 'SourceMarkedTorsionActualCount-1934.exit', 'SourceMarkedTorsionActualCount-1934.log', 'SourceMarkedTorsionActualCount-failed1933.lean.txt', 'SourceMarkedTorsionActualCount.lean', 'SourceMarkedTorsionActualCount1918a.exit', 'SourceMarkedTorsionActualCount1918a.lean.txt', 'SourceMarkedTorsionActualCount1918a.log', 'SourceMarkedTorsionActualCount1918b.exit', 'SourceMarkedTorsionActualCount1918b.lean', 'SourceMarkedTorsionActualCount1918b.log', 'SourceMarkedTorsionGeneratorUnit-1933.exit', 'SourceMarkedTorsionGeneratorUnit-1933.log', 'SourceMarkedTorsionGeneratorUnit-1934.exit', 'SourceMarkedTorsionGeneratorUnit-1934.log', 'SourceMarkedTorsionGeneratorUnit-failed1933.lean.txt', 'SourceMarkedTorsionGeneratorUnit.lean', 'SourceMarkedTorsionGeneratorUnit1926a.exit', 'SourceMarkedTorsionGeneratorUnit1926a.lean', 'SourceMarkedTorsionGeneratorUnit1926a.log', 'SourceMarkedTorsionSignClasses-1933.exit', 'SourceMarkedTorsionSignClasses-1933.log', 'SourceMarkedTorsionSignClasses-1934.exit', 'SourceMarkedTorsionSignClasses-1934.log', 'SourceMarkedTorsionSignClasses-failed1933.lean.txt', 'SourceMarkedTorsionSignClasses.lean', 'SourceMarkedTorsionSignClasses1916a.exit', 'SourceMarkedTorsionSignClasses1916a.lean', 'SourceMarkedTorsionSignClasses1916a.log', 'SourceMarkedTorsionSignedIndex-1933.exit', 'SourceMarkedTorsionSignedIndex-1933.log', 'SourceMarkedTorsionSignedIndex-1934.exit', 'SourceMarkedTorsionSignedIndex-1934.log', 'SourceMarkedTorsionSignedIndex-failed1933.lean.txt', 'SourceMarkedTorsionSignedIndex.lean', 'SourceMarkedTorsionSignedIndex1917a.exit', 'SourceMarkedTorsionSignedIndex1917a.lean.txt', 'SourceMarkedTorsionSignedIndex1917a.log', 'SourceMarkedTorsionSignedIndex1917b.exit', 'SourceMarkedTorsionSignedIndex1917b.lean', 'SourceMarkedTorsionSignedIndex1917b.log', 'SourceTateOriginalJCoordinate-1914.exit', 'SourceTateOriginalJCoordinate-1914.log', 'SourceTateOriginalJCoordinate.lean', 'SourceTateOriginalJCoordinate1900a.exit', 'SourceTateOriginalJCoordinate1900a.lean.txt', 'SourceTateOriginalJCoordinate1900a.log', 'SourceTateOriginalJCoordinate1900b.exit', 'SourceTateOriginalJCoordinate1900b.lean.txt', 'SourceTateOriginalJCoordinate1900b.log', 'SourceTateOriginalJCoordinate1900c.exit', 'SourceTateOriginalJCoordinate1900c.lean.txt', 'SourceTateOriginalJCoordinate1900c.log', 'SourceTateOriginalJCoordinate1900d.exit', 'SourceTateOriginalJCoordinate1900d.lean.txt', 'SourceTateOriginalJCoordinate1900d.log', 'SourceTateOriginalJCoordinate1900e.exit', 'SourceTateOriginalJCoordinate1900e.lean.txt', 'SourceTateOriginalJCoordinate1900e.log', 'SourceTateOriginalJCoordinate1900f.exit', 'SourceTateOriginalJCoordinate1900f.lean.txt', 'SourceTateOriginalJCoordinate1900f.log', 'SourceTateOriginalJCoordinate1900g.exit', 'SourceTateOriginalJCoordinate1900g.lean', 'SourceTateOriginalJCoordinate1900g.log', 'anthropic-gamma-one-point-chart-1846/S_ModularCurve_exists_algHom_qExpFunctionFieldC_gammaH_bot_comp_eq_iff_and_comp_diamondPullbackModL_of_transcendental_j.lean.txt', 'anthropic-gamma-one-point-chart-1846/manifest.json', 'anthropic-primitive-point-orbit-1915/S_AddCommGroup_natCard_torsionOrbit_gammaH_eq_index.lean.txt', 'anthropic-primitive-point-orbit-1915/S_WeierstrassCurve_exists_algEquiv_map_eq_of_addOrderOf_eq_of_transcendental_j.lean.txt', 'anthropic-primitive-point-orbit-1915/sources.json', 'anthropic-primitive-transvection-1919/S_AddAut_exists_mem_apply_eq_of_addOrderOf_eq_of_transvection_mem.lean.txt', 'anthropic-primitive-transvection-1919/S_WeierstrassCurve_exists_algEquiv_map_eq_smul_and_map_eq_smul_add_of_transcendental_j.lean.txt', 'anthropic-primitive-transvection-1919/sources.json', 'anthropic-residue-chart-construction-1751/S_ModularCurve_exists_algHom_qExpFunctionFieldC_gammaH_coe_eq_div_of_map_eq_smul_qExpansion_slash.lean.txt', 'anthropic-residue-chart-construction-1751/S_ModularCurve_exists_natural_diamond_algHom_qExpFunctionFieldC_gammaH_bot_of_transcendental_j.lean.txt', 'anthropic-residue-chart-construction-1751/manifest.json', 'audit_marked_chart_construction_1914.ps1', 'audit_marked_chart_stabilizer_1933.ps1', 'audit_marked_chart_stabilizer_1934.ps1', 'audit_marked_natural_chart_1939.ps1', 'build_marked_chart_construction_canonical_1914.ps1', 'build_marked_chart_stabilizer_canonical_1933.ps1', 'build_marked_chart_stabilizer_canonical_1934.ps1', 'build_marked_natural_chart_canonical_1939.ps1', 'marked-chart-construction-versions-1914.json', 'marked-chart-stabilizer-versions-1933.json', 'marked-chart-stabilizer-versions-1934.json', 'marked-natural-chart-versions-1939.json', 'original-marked-chart-promotion-route-1943.json', 'prepare_marked_chart_construction_audit_1914.py', 'prepare_marked_chart_stabilizer_audit_1933.py', 'prepare_marked_chart_stabilizer_audit_1934.py', 'prepare_marked_natural_chart_audit_1939.py', 'record_marked_chart_construction_1914.py', 'record_marked_chart_stabilizer_1933.py', 'record_marked_chart_stabilizer_1934.py', 'record_marked_natural_chart_1939.py', 'source-marked-chart-construction-1-audit-config.json', 'source-marked-chart-construction-1-reuse-review-20261029.json', 'source-marked-chart-construction-1-scratch-receipt.json', 'source-marked-chart-construction-audit-route-1914.json', 'source-marked-chart-stabilizer-1-audit-config.json', 'source-marked-chart-stabilizer-2-audit-config.json', 'source-marked-chart-stabilizer-2-reuse-review-20261029.json', 'source-marked-chart-stabilizer-2-scratch-receipt.json', 'source-marked-chart-stabilizer-audit-route-1933.json', 'source-marked-chart-stabilizer-audit-route-1934.json', 'source-marked-natural-chart-1-audit-config.json', 'source-marked-natural-chart-1-reuse-review-20261029.json', 'source-marked-natural-chart-1-scratch-receipt.json', 'source-marked-natural-chart-audit-route-1939.json']]
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
supplemental_review_path=r/archive_rel/'original-marked-chart-promotion-route-1943.json'

audit = r / "Extension/Dubon2026/Audit.lean"
at = audit.read_text(encoding="utf-8")
for n in queries:
    assert not re.search(r"``" + re.escape(n) + r"(?=[,\s])", at)
tm, dm = "\n]\n\nprivate def publicConstructions", "\n]\n\nprivate def runAudit"
assert at.count(tm) == at.count(dm) == 1
at = at.replace(tm, "".join("\n  ,``" + n for n in theorems) + tm, 1)
at = at.replace(dm, "".join("\n  ," + chr(96)*2 + n for n in defs) + dm, 1)
research_path = r / "Tools/lean-reuse-audit-20261020.json"
reuse_path = r / "Tools/source-original-marked-chart.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt9450"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> automorphy -> original all-weight characteristic-zero association -> homogeneous Gamma1 Hecke-character realization -> original genus preservation -> reverse genus -> finite elliptic residue fibers -> original-field natural marked-point chart.'
discharged = 'The actual generic elliptic curve has an exact-order marked point and an embedding of the original Gamma1 residue field with matching invariant coordinates. The embedding and point modulo sign have exactly the same Galois stabilizer: native normal-extension lifting, original diamond coordinates, cyclic-quotient correspondence, torsion structure and the proved original residue degree discharge the conjugacy, orbit and index premises. Over the algebraic closure of the generic j field, the resulting chart has exact Galois covariance, exact original diamond covariance, sign invariance and separation up to sign. These final consumers assume no coordinate, stabilizer, transitivity, degree, or point-count certificate. All positive residue characteristics away from the level, including two and three, are retained for levels at least two.'
boundary = 'Descent of this chart to arbitrary fields containing full level-N torsion, finite elliptic-fiber bounds and reverse genus remain open. Original genus preservation, parabolic transfer, exceptional-prime removal, two-dimensional characteristic-zero realization, original all-weight association, remaining local/image/regularity inputs, automorphy and literal higher continuation remain required. Acceptance stays 16/20; DUB-17--20 OPEN; every original source and verification criterion is unchanged.'
status = 'The 33-module scratch scope passes 67 public axiom queries, 103 exhaustive theorem checks, sixteen linters per module and three declaration-value audits with 117 required dependencies, with zero diagnostics. Production aggregate, focused audits and sequential foundation/paper verification of the 9,483-module scope are pending.'
route = 'The October 29 reuse refresh supports a shorter native proof than the references full Tate transvection and matrix-monodromy route. Only the signed point orbit is needed for the exact sign-invariant chart. Native normal extension and cyclic correspondence supply it; equality of stabilizers gives an injective equivariant map. A signed diamond lift at one point proves exact diamond covariance everywhere. The stronger external unsigned transport helper is deferred because this unchanged chart conclusion does not need it. Earlier frozen comments retain their historical source-boundary assessment; this assessment supersedes it. The three audited scopes are promoted by imports only, preserving all mathematical statements, bodies and comments. Exhaustive public/private/generated axiom checks, sixteen linters per module, 117 VALUE dependencies, exact ownership reconciliation and sequential foundation/paper verification are mandatory. Frozen paper, dependency pins and owner-only BAT stay unchanged. External files remain hashed inert references; no foreign module is imported or built.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Original-field natural marked chart and exact stabilizers (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 9,450-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
corrections = []
count = sum(z['exhaustiveTheorems'] for z in certs)
assert count == 103

docpaths = list(dict.fromkeys(r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]))
for f in docpaths:
    assert "\n\n" in f.read_text(encoding="utf-8")
readmes = [(r.parent / "README.md", "Current Project 83 status ("), (repo / "README.md", "Project 83 has an ")]
for f, prefix in readmes:
    assert sum(line.startswith(prefix) for line in f.read_text(encoding="utf-8").splitlines()) == 1
arch = r / "Dubon Architecture.md"
edge = '  TORICPOINT9450["Integral original-field coordinates, actual diamond action and exact-order marked point with matching invariants proved. Full torsion chart, stabilizers, finite elliptic fibers, reverse genus and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourceOriginalMarkedChartProductionAudit9483.lean',p/'source-original-marked-chart-9483-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production9483.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/toric-marked-point-20261029-1901'
registered = {row['path'] for row in c['files']}
for priorFile in priorArchive.iterdir():
    rel = priorFile.relative_to(r).as_posix()
    if priorFile.is_file() and rel not in registered:
        c['files'].append({'path': rel, 'role': 'Tools'})

reportSource = p / 'Dubon Original Marked Chart Assessment 2026-10-29.md'
assert sha(reportSource) == 'E42EEC4C93E5FABB1DD7A3E2A4B677BB6E8EB10464582961E549A7871BCCEB47'
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
    "productionModules": 9483, "modules": newmods, "queries": queries,
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
arch.write_text(arch.read_text(encoding='utf-8').replace(edge,'  TORICPOINT9450["Original-field coordinates, actual diamond action and exact-order marked point proved (DUB-17/18)"] --> MARKEDCHART9483\n  MARKEDCHART9483["Exact point/field stabilizers and generic-field natural marked chart with exact Galois and diamond covariance proved. Arbitrary full-torsion descent, finite elliptic fibers, reverse genus and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'),encoding='utf-8')



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Original-field natural marked chart and exact stabilizers - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-original-marked-chart.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub('  logInfo m!".*"\n', '  logInfo m!"SOURCE ORIGINAL MARKED CHART AUDIT PASS: {count} theorems including private/generated declarations. Original-field generic natural chart and exact stabilizers proved. Finite elliptic bounds, reverse genus and source gates OPEN;16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourceOriginalMarkedChartProductionAudit9483.lean").write_text(out, encoding="utf-8")
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
    target = p / (source.stem + "Production9483.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
(p / "source-original-marked-chart-9483-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 9483, "increment": 33, "queries": 67,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
