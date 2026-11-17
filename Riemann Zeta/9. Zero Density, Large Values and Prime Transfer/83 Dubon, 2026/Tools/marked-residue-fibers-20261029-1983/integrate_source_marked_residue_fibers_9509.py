from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 9483
assert d["appliedSourceOriginalMarkedChart"]["receipt9483"]["exit"] == 0
assert (p / "paper-verification-9483-console.exit").read_text().strip() == "0"
assert (r/'Tools/original-marked-chart-20261029-1943/canonical-evidence-9483.json').exists()
key = "appliedSourceMarkedResidueFibers"
assert key not in d
digests = {'source-marked-algebraic-chart-1-scratch-receipt.json': 'A753AA9704401026CA18678FEFA515AB88CA987F1596E5BB17F80751381E0700', 'source-marked-fiber-chart-2-scratch-receipt.json': 'EBB74AF21B0CFD61E848B5142F169776DB19A06AD7A536DB7059E2F00B8E4A98', 'source-marked-exceptional-fibers-1-scratch-receipt.json': '5F5C09B89D4B3B6D544B8488F13136F8A1583BB3AE5B4463DAFDC127959D19A7'}

for name, digest in digests.items():
    assert sha(p / name) == digest
certs = [json.loads((p / name).read_text(encoding="utf-8")) for name in digests]
mods = [m for z in certs for m in z["modules"]]
queries = [q for z in certs for q in z["queries"]]
theorems = [q for z in certs for q in z["theoremRegistrations"]]
defs = [q for z in certs for q in z["constructionRegistrations"]]
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (26, 26, 34, 33, 1)
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
archive_rel='Tools/marked-residue-fibers-20261029-1983'
evidence=[p/n for n in ['Dubon Marked Residue Fibers Assessment 2026-10-29.md', 'SourceMarkedAlgebraicChartAudit1.exit', 'SourceMarkedAlgebraicChartAudit1.lean', 'SourceMarkedAlgebraicChartAudit1.log', 'SourceMarkedAlgebraicChartDependencyAudit1.exit', 'SourceMarkedAlgebraicChartDependencyAudit1.lean', 'SourceMarkedAlgebraicChartDependencyAudit1.log', 'SourceMarkedAlgebraicChartScratchOwnership1953.exit', 'SourceMarkedAlgebraicChartScratchOwnership1953.lean', 'SourceMarkedAlgebraicChartScratchOwnership1953.log', 'SourceMarkedChartFiberSurjection-1960.exit', 'SourceMarkedChartFiberSurjection-1960.log', 'SourceMarkedChartFiberSurjection.lean', 'SourceMarkedChartFiberSurjection1958a.exit', 'SourceMarkedChartFiberSurjection1958a.lean.txt', 'SourceMarkedChartFiberSurjection1958a.log', 'SourceMarkedChartFiberSurjection1958b.exit', 'SourceMarkedChartFiberSurjection1958b.lean', 'SourceMarkedChartFiberSurjection1958b.log', 'SourceMarkedChartNormalExhaustion-1953.exit', 'SourceMarkedChartNormalExhaustion-1953.log', 'SourceMarkedChartNormalExhaustion.lean', 'SourceMarkedChartNormalExhaustion1951a.exit', 'SourceMarkedChartNormalExhaustion1951a.lean', 'SourceMarkedChartNormalExhaustion1951a.log', 'SourceMarkedChartPlaceOrbits-1960.exit', 'SourceMarkedChartPlaceOrbits-1960.log', 'SourceMarkedChartPlaceOrbits.lean', 'SourceMarkedChartPlaceOrbits1954a.exit', 'SourceMarkedChartPlaceOrbits1954a.lean.txt', 'SourceMarkedChartPlaceOrbits1954a.log', 'SourceMarkedChartPlaceOrbits1954b.exit', 'SourceMarkedChartPlaceOrbits1954b.lean', 'SourceMarkedChartPlaceOrbits1954b.log', 'SourceMarkedExceptionalFibersAudit1.exit', 'SourceMarkedExceptionalFibersAudit1.lean', 'SourceMarkedExceptionalFibersAudit1.log', 'SourceMarkedExceptionalFibersDependencyAudit1.exit', 'SourceMarkedExceptionalFibersDependencyAudit1.lean', 'SourceMarkedExceptionalFibersDependencyAudit1.log', 'SourceMarkedExceptionalFibersScratchOwnership1974.exit', 'SourceMarkedExceptionalFibersScratchOwnership1974.lean', 'SourceMarkedExceptionalFibersScratchOwnership1974.log', 'SourceMarkedFiberChartAudit1.exit', 'SourceMarkedFiberChartAudit1.lean', 'SourceMarkedFiberChartAudit1.log', 'SourceMarkedFiberChartDependencyAudit1.exit', 'SourceMarkedFiberChartDependencyAudit1.lean.txt', 'SourceMarkedFiberChartDependencyAudit1.log', 'SourceMarkedFiberChartDependencyAudit2.exit', 'SourceMarkedFiberChartDependencyAudit2.lean', 'SourceMarkedFiberChartDependencyAudit2.log', 'SourceMarkedFiberChartScratchOwnership1963.exit', 'SourceMarkedFiberChartScratchOwnership1963.lean', 'SourceMarkedFiberChartScratchOwnership1963.log', 'SourceMarkedFullInertiaLifts-1974.exit', 'SourceMarkedFullInertiaLifts-1974.log', 'SourceMarkedFullInertiaLifts.lean', 'SourceMarkedFullInertiaLifts1973a.exit', 'SourceMarkedFullInertiaLifts1973a.lean', 'SourceMarkedFullInertiaLifts1973a.log', 'SourceMarkedFullTorsionNonempty-1960.exit', 'SourceMarkedFullTorsionNonempty-1960.log', 'SourceMarkedFullTorsionNonempty.lean', 'SourceMarkedFullTorsionNonempty1957a.exit', 'SourceMarkedFullTorsionNonempty1957a.lean.txt', 'SourceMarkedFullTorsionNonempty1957a.log', 'SourceMarkedFullTorsionNonempty1957b.exit', 'SourceMarkedFullTorsionNonempty1957b.lean.txt', 'SourceMarkedFullTorsionNonempty1957b.log', 'SourceMarkedFullTorsionNonempty1957c.exit', 'SourceMarkedFullTorsionNonempty1957c.lean', 'SourceMarkedFullTorsionNonempty1957c.log', 'SourceMarkedFullTorsionPointLift-1953.exit', 'SourceMarkedFullTorsionPointLift-1953.log', 'SourceMarkedFullTorsionPointLift.lean', 'SourceMarkedFullTorsionPointLift1949a.exit', 'SourceMarkedFullTorsionPointLift1949a.lean', 'SourceMarkedFullTorsionPointLift1949a.log', 'SourceMarkedOriginalAlgebraicChart-1953.exit', 'SourceMarkedOriginalAlgebraicChart-1953.log', 'SourceMarkedOriginalAlgebraicChart.lean', 'SourceMarkedOriginalAlgebraicChart1948a.exit', 'SourceMarkedOriginalAlgebraicChart1948a.lean.txt', 'SourceMarkedOriginalAlgebraicChart1948a.log', 'SourceMarkedOriginalAlgebraicChart1948b.exit', 'SourceMarkedOriginalAlgebraicChart1948b.lean.txt', 'SourceMarkedOriginalAlgebraicChart1948b.log', 'SourceMarkedOriginalAlgebraicChart1948c.exit', 'SourceMarkedOriginalAlgebraicChart1948c.lean.txt', 'SourceMarkedOriginalAlgebraicChart1948c.log', 'SourceMarkedOriginalAlgebraicChart1948d.exit', 'SourceMarkedOriginalAlgebraicChart1948d.lean', 'SourceMarkedOriginalAlgebraicChart1948d.log', 'SourceMarkedOriginalFiberChart-1960.exit', 'SourceMarkedOriginalFiberChart-1960.log', 'SourceMarkedOriginalFiberChart.lean', 'SourceMarkedOriginalFiberChart1959a.exit', 'SourceMarkedOriginalFiberChart1959a.lean', 'SourceMarkedOriginalFiberChart1959a.log', 'SourceMarkedOriginalFullTorsionChart-1953.exit', 'SourceMarkedOriginalFullTorsionChart-1953.log', 'SourceMarkedOriginalFullTorsionChart.lean', 'SourceMarkedOriginalFullTorsionChart1952a.exit', 'SourceMarkedOriginalFullTorsionChart1952a.lean', 'SourceMarkedOriginalFullTorsionChart1952a.log', 'SourceMarkedOriginalOfJChart-1960.exit', 'SourceMarkedOriginalOfJChart-1960.log', 'SourceMarkedOriginalOfJChart.lean', 'SourceMarkedOriginalOfJChart1955a.exit', 'SourceMarkedOriginalOfJChart1955a.lean.txt', 'SourceMarkedOriginalOfJChart1955a.log', 'SourceMarkedOriginalOfJChart1955b.exit', 'SourceMarkedOriginalOfJChart1955b.lean.txt', 'SourceMarkedOriginalOfJChart1955b.log', 'SourceMarkedOriginalOfJChart1955c.exit', 'SourceMarkedOriginalOfJChart1955c.lean.txt', 'SourceMarkedOriginalOfJChart1955c.log', 'SourceMarkedOriginalOfJChart1955d.exit', 'SourceMarkedOriginalOfJChart1955d.lean.txt', 'SourceMarkedOriginalOfJChart1955d.log', 'SourceMarkedOriginalOfJChart1955e.exit', 'SourceMarkedOriginalOfJChart1955e.lean', 'SourceMarkedOriginalOfJChart1955e.log', 'SourceMarkedOriginalPlaceChart-1960.exit', 'SourceMarkedOriginalPlaceChart-1960.log', 'SourceMarkedOriginalPlaceChart.lean', 'SourceMarkedOriginalPlaceChart1956a.exit', 'SourceMarkedOriginalPlaceChart1956a.lean', 'SourceMarkedOriginalPlaceChart1956a.log', 'SourceMarkedOriginalResidueFiberFive-1974.exit', 'SourceMarkedOriginalResidueFiberFive-1974.log', 'SourceMarkedOriginalResidueFiberFive.lean', 'SourceMarkedOriginalResidueFiberFive1969a.exit', 'SourceMarkedOriginalResidueFiberFive1969a.lean.txt', 'SourceMarkedOriginalResidueFiberFive1969a.log', 'SourceMarkedOriginalResidueFiberFive1969b.exit', 'SourceMarkedOriginalResidueFiberFive1969b.lean.txt', 'SourceMarkedOriginalResidueFiberFive1969b.log', 'SourceMarkedOriginalResidueFiberFive1969c.exit', 'SourceMarkedOriginalResidueFiberFive1969c.lean.txt', 'SourceMarkedOriginalResidueFiberFive1969c.log', 'SourceMarkedOriginalResidueFiberFive1969d.exit', 'SourceMarkedOriginalResidueFiberFive1969d.lean.txt', 'SourceMarkedOriginalResidueFiberFive1969d.log', 'SourceMarkedOriginalResidueFiberFive1969e.exit', 'SourceMarkedOriginalResidueFiberFive1969e.lean', 'SourceMarkedOriginalResidueFiberFive1969e.log', 'SourceMarkedOriginalResidueFiberThree-1974.exit', 'SourceMarkedOriginalResidueFiberThree-1974.log', 'SourceMarkedOriginalResidueFiberThree.lean', 'SourceMarkedOriginalResidueFiberThree1972a.exit', 'SourceMarkedOriginalResidueFiberThree1972a.lean.txt', 'SourceMarkedOriginalResidueFiberThree1972a.log', 'SourceMarkedOriginalResidueFiberThree1972b.exit', 'SourceMarkedOriginalResidueFiberThree1972b.lean.txt', 'SourceMarkedOriginalResidueFiberThree1972b.log', 'SourceMarkedOriginalResidueFiberThree1972c.exit', 'SourceMarkedOriginalResidueFiberThree1972c.lean', 'SourceMarkedOriginalResidueFiberThree1972c.log', 'SourceMarkedOriginalResidueFiberTwo-1974.exit', 'SourceMarkedOriginalResidueFiberTwo-1974.log', 'SourceMarkedOriginalResidueFiberTwo.lean', 'SourceMarkedOriginalResidueFiberTwo1971a.exit', 'SourceMarkedOriginalResidueFiberTwo1971a.lean.txt', 'SourceMarkedOriginalResidueFiberTwo1971a.log', 'SourceMarkedOriginalResidueFiberTwo1971b.exit', 'SourceMarkedOriginalResidueFiberTwo1971b.lean.txt', 'SourceMarkedOriginalResidueFiberTwo1971b.log', 'SourceMarkedOriginalResidueFiberTwo1971c.exit', 'SourceMarkedOriginalResidueFiberTwo1971c.lean', 'SourceMarkedOriginalResidueFiberTwo1971c.log', 'SourceMarkedOriginalSeparability-1953.exit', 'SourceMarkedOriginalSeparability-1953.log', 'SourceMarkedOriginalSeparability.lean', 'SourceMarkedOriginalSeparability1944a.exit', 'SourceMarkedOriginalSeparability1944a.lean', 'SourceMarkedOriginalSeparability1944a.log', 'SourceMarkedOriginalSeparability1944b.exit', 'SourceMarkedOriginalSeparability1944b.lean', 'SourceMarkedOriginalSeparability1944b.log', 'SourceMarkedOriginalTameFiberBounds-1974.exit', 'SourceMarkedOriginalTameFiberBounds-1974.log', 'SourceMarkedOriginalTameFiberBounds.lean', 'SourceMarkedOriginalTameFiberBounds1970a.exit', 'SourceMarkedOriginalTameFiberBounds1970a.lean.txt', 'SourceMarkedOriginalTameFiberBounds1970a.log', 'SourceMarkedOriginalTameFiberBounds1970b.exit', 'SourceMarkedOriginalTameFiberBounds1970b.lean', 'SourceMarkedOriginalTameFiberBounds1970b.log', 'SourceMarkedPeriodicFiberBound-1974.exit', 'SourceMarkedPeriodicFiberBound-1974.log', 'SourceMarkedPeriodicFiberBound.lean', 'SourceMarkedPeriodicFiberBound1965a.exit', 'SourceMarkedPeriodicFiberBound1965a.lean', 'SourceMarkedPeriodicFiberBound1965a.log', 'SourceMarkedQuadraticFiberBounds-1974.exit', 'SourceMarkedQuadraticFiberBounds-1974.log', 'SourceMarkedQuadraticFiberBounds.lean', 'SourceMarkedQuadraticFiberBounds1967a.exit', 'SourceMarkedQuadraticFiberBounds1967a.lean.txt', 'SourceMarkedQuadraticFiberBounds1967a.log', 'SourceMarkedQuadraticFiberBounds1967b.exit', 'SourceMarkedQuadraticFiberBounds1967b.lean', 'SourceMarkedQuadraticFiberBounds1967b.log', 'SourceMarkedQuadraticFiberBounds1967c.exit', 'SourceMarkedQuadraticFiberBounds1967c.lean', 'SourceMarkedQuadraticFiberBounds1967c.log', 'SourceMarkedRationalPointDescent-1953.exit', 'SourceMarkedRationalPointDescent-1953.log', 'SourceMarkedRationalPointDescent.lean', 'SourceMarkedRationalPointDescent1947a.exit', 'SourceMarkedRationalPointDescent1947a.lean', 'SourceMarkedRationalPointDescent1947a.log', 'SourceMarkedRationalPointDescent1947b.exit', 'SourceMarkedRationalPointDescent1947b.lean', 'SourceMarkedRationalPointDescent1947b.log', 'SourceMarkedReducedFiberChart-1974.exit', 'SourceMarkedReducedFiberChart-1974.log', 'SourceMarkedReducedFiberChart.lean', 'SourceMarkedReducedFiberChart1968a.exit', 'SourceMarkedReducedFiberChart1968a.lean.txt', 'SourceMarkedReducedFiberChart1968a.log', 'SourceMarkedReducedFiberChart1968b.exit', 'SourceMarkedReducedFiberChart1968b.lean.txt', 'SourceMarkedReducedFiberChart1968b.log', 'SourceMarkedReducedFiberChart1968c.exit', 'SourceMarkedReducedFiberChart1968c.lean', 'SourceMarkedReducedFiberChart1968c.log', 'SourceMarkedSeparableChartValues-1953.exit', 'SourceMarkedSeparableChartValues-1953.log', 'SourceMarkedSeparableChartValues.lean', 'SourceMarkedSeparableChartValues1945a.exit', 'SourceMarkedSeparableChartValues1945a.lean', 'SourceMarkedSeparableChartValues1945a.log', 'SourceMarkedSeparableChartValues1945b.exit', 'SourceMarkedSeparableChartValues1945b.lean', 'SourceMarkedSeparableChartValues1945b.log', 'SourceMarkedSeparableEmbeddingDescent-1953.exit', 'SourceMarkedSeparableEmbeddingDescent-1953.log', 'SourceMarkedSeparableEmbeddingDescent.lean', 'SourceMarkedSeparableEmbeddingDescent1946a.exit', 'SourceMarkedSeparableEmbeddingDescent1946a.lean', 'SourceMarkedSeparableEmbeddingDescent1946a.log', 'SourceMarkedSeparableEmbeddingDescent1946b.exit', 'SourceMarkedSeparableEmbeddingDescent1946b.lean', 'SourceMarkedSeparableEmbeddingDescent1946b.log', 'SourceMarkedSignFiberFactor-1974.exit', 'SourceMarkedSignFiberFactor-1974.log', 'SourceMarkedSignFiberFactor.lean', 'SourceMarkedSignFiberFactor1964a.exit', 'SourceMarkedSignFiberFactor1964a.lean.txt', 'SourceMarkedSignFiberFactor1964a.log', 'SourceMarkedSignFiberFactor1964b.exit', 'SourceMarkedSignFiberFactor1964b.lean', 'SourceMarkedSignFiberFactor1964b.log', 'SourceMarkedSignFiberFactor1964c.exit', 'SourceMarkedSignFiberFactor1964c.lean', 'SourceMarkedSignFiberFactor1964c.log', 'SourceMarkedSignFreeOrbits-1974.exit', 'SourceMarkedSignFreeOrbits-1974.log', 'SourceMarkedSignFreeOrbits.lean', 'SourceMarkedSignFreeOrbits1962a.exit', 'SourceMarkedSignFreeOrbits1962a.lean.txt', 'SourceMarkedSignFreeOrbits1962a.log', 'SourceMarkedSignFreeOrbits1962b.exit', 'SourceMarkedSignFreeOrbits1962b.lean', 'SourceMarkedSignFreeOrbits1962b.log', 'SourceMarkedSignFreeOrbits1962c.exit', 'SourceMarkedSignFreeOrbits1962c.lean', 'SourceMarkedSignFreeOrbits1962c.log', 'SourceMarkedSignPermutation-1974.exit', 'SourceMarkedSignPermutation-1974.log', 'SourceMarkedSignPermutation.lean', 'SourceMarkedSignPermutation1961a.exit', 'SourceMarkedSignPermutation1961a.lean.txt', 'SourceMarkedSignPermutation1961a.log', 'SourceMarkedSignPermutation1961b.exit', 'SourceMarkedSignPermutation1961b.lean', 'SourceMarkedSignPermutation1961b.log', 'SourceMarkedSignPermutation1961c.exit', 'SourceMarkedSignPermutation1961c.lean', 'SourceMarkedSignPermutation1961c.log', 'SourceMarkedTorsionReductionEquiv-1974.exit', 'SourceMarkedTorsionReductionEquiv-1974.log', 'SourceMarkedTorsionReductionEquiv.lean', 'SourceMarkedTorsionReductionEquiv1966a.exit', 'SourceMarkedTorsionReductionEquiv1966a.lean.txt', 'SourceMarkedTorsionReductionEquiv1966a.log', 'SourceMarkedTorsionReductionEquiv1966b.exit', 'SourceMarkedTorsionReductionEquiv1966b.lean', 'SourceMarkedTorsionReductionEquiv1966b.log', 'anthropic-diamond-place-charts-1746/S_ModularCurve_exists_injective_doubleCoset_forall_diamondPullbackModL_smul_place_eq_of_ord_pos.lean.txt', 'audit_marked_algebraic_chart_1953.ps1', 'audit_marked_exceptional_fibers_1974.ps1', 'audit_marked_fiber_chart_1960.ps1', 'audit_marked_fiber_chart_1963.ps1', 'build_marked_algebraic_chart_canonical_1953.ps1', 'build_marked_exceptional_fibers_canonical_1974.ps1', 'build_marked_fiber_chart_canonical_1960.ps1', 'marked-algebraic-chart-route-1950.json', 'marked-algebraic-chart-versions-1953.json', 'marked-exceptional-fibers-versions-1974.json', 'marked-fiber-chart-audit-successor-1963.json', 'marked-fiber-chart-versions-1960.json', 'marked-residue-fibers-promotion-route-1983.json', 'prepare_marked_algebraic_chart_audit_1953.py', 'prepare_marked_exceptional_fibers_audit_1974.py', 'prepare_marked_fiber_chart_audit_1960.py', 'record_marked_algebraic_chart_1953.py', 'record_marked_exceptional_fibers_1974.py', 'record_marked_fiber_chart_1960.py', 'record_marked_fiber_chart_1963.py', 'source-marked-algebraic-chart-1-audit-config.json', 'source-marked-algebraic-chart-1-reuse-review-20261029.json', 'source-marked-algebraic-chart-1-scratch-receipt.json', 'source-marked-algebraic-chart-audit-route-1953.json', 'source-marked-exceptional-fibers-1-audit-config.json', 'source-marked-exceptional-fibers-1-reuse-review-20261029.json', 'source-marked-exceptional-fibers-1-scratch-receipt.json', 'source-marked-exceptional-fibers-audit-route-1974.json', 'source-marked-fiber-chart-1-audit-config.json', 'source-marked-fiber-chart-2-audit-config.json', 'source-marked-fiber-chart-2-reuse-review-20261029.json', 'source-marked-fiber-chart-2-scratch-receipt.json', 'source-marked-fiber-chart-audit-route-1960.json']]
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
supplemental_review_path=r/archive_rel/'marked-residue-fibers-promotion-route-1983.json'

audit = r / "Extension/Dubon2026/Audit.lean"
at = audit.read_text(encoding="utf-8")
for n in queries:
    assert not re.search(r"``" + re.escape(n) + r"(?=[,\s])", at)
tm, dm = "\n]\n\nprivate def publicConstructions", "\n]\n\nprivate def runAudit"
assert at.count(tm) == at.count(dm) == 1
at = at.replace(tm, "".join("\n  ,``" + n for n in theorems) + tm, 1)
at = at.replace(dm, "".join("\n  ," + chr(96)*2 + n for n in defs) + dm, 1)
research_path = r / "Tools/lean-reuse-audit-20261020.json"
reuse_path = r / "Tools/source-marked-residue-fibers.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt9483"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> automorphy -> original all-weight characteristic-zero association -> homogeneous Gamma1 Hecke-character realization -> original genus preservation -> reverse genus -> actual finite elliptic residue fibers.'
discharged = 'The original Gamma1 marked-point chart descends to a finite normal field containing full level-N torsion and exhausts all normalized embeddings. Native place lifting and inertia identify its actual finite j fibers, with exact original diamond covariance. Native full-inertia specialization and torsion reduction then construct actual residue-point fiber charts in every positive residue characteristic away from the level, including two and three, for N at least two. For N greater than three and residue characteristic at least five, twice the cardinality of the original j=1728 fiber and three times the cardinality of the original j=0 fiber are each at most the signed Gamma1 index. These bounds have no chart, torsion-count, stabilizer, finite-field or inertia-lift premises.'
boundary = 'Wild characteristic-two and characteristic-three numerical fiber/different census, the remaining small levels and reverse genus remain open in production. Original genus preservation, parabolic transfer, exceptional-prime removal, two-dimensional characteristic-zero realization, original all-weight association, remaining local/image/regularity inputs, automorphy and literal higher continuation remain required. Acceptance stays 16/20; DUB-17--20 OPEN; every original source and verification criterion is unchanged.'
status = 'The 26-module scratch scope passes 34 public axiom queries, 63 exhaustive theorem checks, sixteen linters per module and three declaration-value audits with 65 required dependencies, with zero diagnostics. Production aggregate, focused audits and sequential foundation/paper verification of the 9,509-module scope are pending.'
route = 'The October 29 reuse search identifies the exact finite-normal-field ofJ(X) consumer of the original chart. Native separable descent and normal embedding exhaustion suffice; arbitrary coefficient-curve generalizations are deferred. The native quartic and cubic point identities make their actions free on exact-order point sign classes for N greater than three, giving the two tame fiber bounds without an adapted torsion basis. In characteristics two and three native full inertia constructs the residue-point charts; their numerical census remains separate. Three scratch scopes pass 65 proof-VALUE dependencies, exhaustive public/private/generated axiom checks and sixteen linters per module. The signClassesEquiv_pair evaluation lemma is separately axiom checked, not claimed as a consumed VALUE dependency. The failed first fiber dependency audit and its fresh successor are preserved: transitive versioned upstream modules were added to traversal without removing any required edge or altering mathematics. Promotion changes imports only; statements, bodies and comments remain frozen. Exact ownership reconciliation and sequential foundation/paper verification remain mandatory. Paper, root pins, proof limits and owner-only BAT are unchanged.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Actual original Gamma1 residue fibers and tame bounds (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 9,483-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
corrections = []
count = sum(z['exhaustiveTheorems'] for z in certs)
assert count == 63

docpaths = list(dict.fromkeys(r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]))
for f in docpaths:
    assert "\n\n" in f.read_text(encoding="utf-8")
readmes = [(r.parent / "README.md", "Current Project 83 status ("), (repo / "README.md", "Project 83 has an ")]
for f, prefix in readmes:
    assert sum(line.startswith(prefix) for line in f.read_text(encoding="utf-8").splitlines()) == 1
arch = r / "Dubon Architecture.md"
edge = '  MARKEDCHART9483["Exact point/field stabilizers and generic-field natural marked chart with exact Galois and diamond covariance proved. Arbitrary full-torsion descent, finite elliptic fibers, reverse genus and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourceMarkedResidueFibersProductionAudit9509.lean',p/'source-marked-residue-fibers-9509-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production9509.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/original-marked-chart-20261029-1943'
registered = {row['path'] for row in c['files']}
for priorFile in priorArchive.iterdir():
    rel = priorFile.relative_to(r).as_posix()
    if priorFile.is_file() and rel not in registered:
        c['files'].append({'path': rel, 'role': 'Tools'})

reportSource = p / 'Dubon Marked Residue Fibers Assessment 2026-10-29.md'
assert sha(reportSource) == '7909F6B3CB93341A5202D81E1B07C3642C21A6A38F7D02A9541174A9F0F5BB5B'
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
    "productionModules": 9509, "modules": newmods, "queries": queries,
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
arch.write_text(arch.read_text(encoding='utf-8').replace(edge,'  MARKEDCHART9483["Original generic marked chart and exact stabilizers proved (DUB-17/18)"] --> RESIDUEFIBERS9509\n  RESIDUEFIBERS9509["Actual original Gamma1 residue charts in all characteristics away from the level; tame elliptic fiber bounds for N greater than three proved. Wild census, small levels, reverse genus and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'),encoding='utf-8')



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Actual original Gamma1 residue fibers and tame bounds - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-marked-residue-fibers.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub('  logInfo m!".*"\n', '  logInfo m!"SOURCE MARKED RESIDUE FIBERS AUDIT PASS: {count} theorems including private/generated declarations. Actual original residue charts and tame elliptic fiber bounds proved. Wild census, small levels, reverse genus and source gates OPEN;16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourceMarkedResidueFibersProductionAudit9509.lean").write_text(out, encoding="utf-8")
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
    target = p / (source.stem + "Production9509.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
(p / "source-marked-residue-fibers-9509-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 9509, "increment": 26, "queries": 34,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
