from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 9374
assert d["appliedSourceOriginalResidueCuspCharts"]["receipt9374"]["exit"] == 0
assert (p / "paper-verification-9374-console.exit").read_text().strip() == "0"
assert (r/'Tools/original-residue-cusp-charts-20261029-1800/canonical-evidence-9374.json').exists()
key = "appliedSourceOriginalResidueCuspBounds"
assert key not in d
digests = {'source-actual-residue-cusp-stabilizer-1-scratch-receipt.json': 'B5D4B824191EF8D84E8553C0F02FC5A0C88BD13019819ABEC3A52976244BE310', 'source-original-residue-labeled-cusp-1-scratch-receipt.json': 'BD4AD05D63EC51B39FCC74E4CB6E72068A3CB176DD7BDE6738D1A4940F4458FD', 'source-original-residue-cusp-fiber-1-scratch-receipt.json': 'D145C006E944630241341ACA66C0CE03E75A10F58E1DC97A8DB38264FC80F33A', 'source-original-residue-cusp-count-2-scratch-receipt.json': '36A5D7B1F7872D151C5D2BA63C658F09B1FC26705628A99EAA51E0C480B059BB'}

for name, digest in digests.items():
    assert sha(p / name) == digest
certs = [json.loads((p / name).read_text(encoding="utf-8")) for name in digests]
mods = [m for z in certs for m in z["modules"]]
queries = [q for z in certs for q in z["queries"]]
theorems = [q for z in certs for q in z["theoremRegistrations"]]
defs = [q for z in certs for q in z["constructionRegistrations"]]
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (36, 36, 57, 51, 6)
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
archive_rel='Tools/original-residue-cusp-bounds-20261029-1854'
evidence=[p/n for n in ['Dubon Actual Residue Cusp Stabilizer Assessment 2026-10-29.md', 'Dubon Original Residue Cusp Count Assessment 2026-10-29.md', 'Dubon Original Residue Cusp Fiber Assessment 2026-10-29.md', 'Dubon Original Residue Labeled Cusp Assessment 2026-10-29.md', 'SourceActualResidueCuspStabilizerAudit1.exit', 'SourceActualResidueCuspStabilizerAudit1.lean', 'SourceActualResidueCuspStabilizerAudit1.log', 'SourceActualResidueCuspStabilizerDependencyAudit1.exit', 'SourceActualResidueCuspStabilizerDependencyAudit1.lean', 'SourceActualResidueCuspStabilizerDependencyAudit1.log', 'SourceActualResidueCuspStabilizerScratchOwnership1813.exit', 'SourceActualResidueCuspStabilizerScratchOwnership1813.lean', 'SourceActualResidueCuspStabilizerScratchOwnership1813.log', 'SourceIntegralDiamondNormalizedAction-1813.exit', 'SourceIntegralDiamondNormalizedAction-1813.log', 'SourceIntegralDiamondNormalizedAction.lean', 'SourceIntegralDiamondNormalizedAction1798a.exit', 'SourceIntegralDiamondNormalizedAction1798a.lean.txt', 'SourceIntegralDiamondNormalizedAction1798a.log', 'SourceIntegralDiamondNormalizedAction1798b.exit', 'SourceIntegralDiamondNormalizedAction1798b.lean.txt', 'SourceIntegralDiamondNormalizedAction1798b.log', 'SourceIntegralDiamondNormalizedAction1798c.exit', 'SourceIntegralDiamondNormalizedAction1798c.lean', 'SourceIntegralDiamondNormalizedAction1798c.log', 'SourceIntegralDiamondNormalizedAction1801a.exit', 'SourceIntegralDiamondNormalizedAction1801a.lean', 'SourceIntegralDiamondNormalizedAction1801a.log', 'SourceIntegralDiamondScalarNormalizedAction-1813.exit', 'SourceIntegralDiamondScalarNormalizedAction-1813.log', 'SourceIntegralDiamondScalarNormalizedAction.lean', 'SourceIntegralDiamondScalarNormalizedAction1803a.exit', 'SourceIntegralDiamondScalarNormalizedAction1803a.lean', 'SourceIntegralDiamondScalarNormalizedAction1803a.log', 'SourceIntegralSlashCuspCoordinate-1830.exit', 'SourceIntegralSlashCuspCoordinate-1830.log', 'SourceIntegralSlashCuspCoordinate.lean', 'SourceIntegralSlashCuspCoordinate1820a.exit', 'SourceIntegralSlashCuspCoordinate1820a.lean', 'SourceIntegralSlashCuspCoordinate1820a.log', 'SourceIntegralSlashCuspTriangular-1830.exit', 'SourceIntegralSlashCuspTriangular-1830.log', 'SourceIntegralSlashCuspTriangular.lean', 'SourceIntegralSlashCuspTriangular1812a.exit', 'SourceIntegralSlashCuspTriangular1812a.lean.txt', 'SourceIntegralSlashCuspTriangular1812a.log', 'SourceIntegralSlashCuspTriangular1812b.exit', 'SourceIntegralSlashCuspTriangular1812b.lean', 'SourceIntegralSlashCuspTriangular1812b.log', 'SourceIntegralSlashDiamondGenerator-1813.exit', 'SourceIntegralSlashDiamondGenerator-1813.log', 'SourceIntegralSlashDiamondGenerator.lean', 'SourceIntegralSlashDiamondGenerator1804a.exit', 'SourceIntegralSlashDiamondGenerator1804a.lean', 'SourceIntegralSlashDiamondGenerator1804a.log', 'SourceIntegralSlashDiamondStabilizer-1813.exit', 'SourceIntegralSlashDiamondStabilizer-1813.log', 'SourceIntegralSlashDiamondStabilizer.lean', 'SourceIntegralSlashDiamondStabilizer1805a.exit', 'SourceIntegralSlashDiamondStabilizer1805a.lean', 'SourceIntegralSlashDiamondStabilizer1805a.log', 'SourceIntegralSlashFieldDiamondCovariance-1845.exit', 'SourceIntegralSlashFieldDiamondCovariance-1845.log', 'SourceIntegralSlashFieldDiamondCovariance.lean', 'SourceIntegralSlashFieldDiamondCovariance1831a.exit', 'SourceIntegralSlashFieldDiamondCovariance1831a.lean', 'SourceIntegralSlashFieldDiamondCovariance1831a.log', 'SourceIntegralSlashFieldNormalizedRatio-1813.exit', 'SourceIntegralSlashFieldNormalizedRatio-1813.log', 'SourceIntegralSlashFieldNormalizedRatio.lean', 'SourceIntegralSlashFieldNormalizedRatio1799a.exit', 'SourceIntegralSlashFieldNormalizedRatio1799a.lean.txt', 'SourceIntegralSlashFieldNormalizedRatio1799a.log', 'SourceIntegralSlashFieldNormalizedRatio1799b.exit', 'SourceIntegralSlashFieldNormalizedRatio1799b.lean', 'SourceIntegralSlashFieldNormalizedRatio1799b.log', 'SourceIntegralSlashFieldNormalizedRatio1802a.exit', 'SourceIntegralSlashFieldNormalizedRatio1802a.lean', 'SourceIntegralSlashFieldNormalizedRatio1802a.log', 'SourceIntegralSlashRaisedCuspCoefficients-1830.exit', 'SourceIntegralSlashRaisedCuspCoefficients-1830.log', 'SourceIntegralSlashRaisedCuspCoefficients.lean', 'SourceIntegralSlashRaisedCuspCoefficients1816a.exit', 'SourceIntegralSlashRaisedCuspCoefficients1816a.lean.txt', 'SourceIntegralSlashRaisedCuspCoefficients1816a.log', 'SourceIntegralSlashRaisedCuspCoefficients1816b.exit', 'SourceIntegralSlashRaisedCuspCoefficients1816b.lean', 'SourceIntegralSlashRaisedCuspCoefficients1816b.log', 'SourceIntegralSlashRaisedCuspCoordinate-1830.exit', 'SourceIntegralSlashRaisedCuspCoordinate-1830.log', 'SourceIntegralSlashRaisedCuspCoordinate.lean', 'SourceIntegralSlashRaisedCuspCoordinate1819a.exit', 'SourceIntegralSlashRaisedCuspCoordinate1819a.lean.txt', 'SourceIntegralSlashRaisedCuspCoordinate1819a.log', 'SourceIntegralSlashRaisedCuspCoordinate1819b.exit', 'SourceIntegralSlashRaisedCuspCoordinate1819b.lean', 'SourceIntegralSlashRaisedCuspCoordinate1819b.log', 'SourceIntegralSlashRaisedCuspFormula-1830.exit', 'SourceIntegralSlashRaisedCuspFormula-1830.log', 'SourceIntegralSlashRaisedCuspFormula.lean', 'SourceIntegralSlashRaisedCuspFormula1814a.exit', 'SourceIntegralSlashRaisedCuspFormula1814a.lean', 'SourceIntegralSlashRaisedCuspFormula1814a.log', 'SourceIntegralSlashRaisedCuspLaurent-1830.exit', 'SourceIntegralSlashRaisedCuspLaurent-1830.log', 'SourceIntegralSlashRaisedCuspLaurent.lean', 'SourceIntegralSlashRaisedCuspLaurent1818a.exit', 'SourceIntegralSlashRaisedCuspLaurent1818a.lean.txt', 'SourceIntegralSlashRaisedCuspLaurent1818a.log', 'SourceIntegralSlashRaisedCuspLaurent1818b.exit', 'SourceIntegralSlashRaisedCuspLaurent1818b.lean', 'SourceIntegralSlashRaisedCuspLaurent1818b.log', 'SourceIntegralSlashRaisedCuspReduction-1830.exit', 'SourceIntegralSlashRaisedCuspReduction-1830.log', 'SourceIntegralSlashRaisedCuspReduction.lean', 'SourceIntegralSlashRaisedCuspReduction1817a.exit', 'SourceIntegralSlashRaisedCuspReduction1817a.lean', 'SourceIntegralSlashRaisedCuspReduction1817a.log', 'SourceIntegralSlashRaisedLevelOne-1830.exit', 'SourceIntegralSlashRaisedLevelOne-1830.log', 'SourceIntegralSlashRaisedLevelOne.lean', 'SourceIntegralSlashRaisedLevelOne1811a.exit', 'SourceIntegralSlashRaisedLevelOne1811a.lean.txt', 'SourceIntegralSlashRaisedLevelOne1811a.log', 'SourceIntegralSlashRaisedLevelOne1811b.exit', 'SourceIntegralSlashRaisedLevelOne1811b.lean', 'SourceIntegralSlashRaisedLevelOne1811b.log', 'SourceIntegralSlashTriangularParameter-1830.exit', 'SourceIntegralSlashTriangularParameter-1830.log', 'SourceIntegralSlashTriangularParameter.lean', 'SourceIntegralSlashTriangularParameter1815a.exit', 'SourceIntegralSlashTriangularParameter1815a.lean', 'SourceIntegralSlashTriangularParameter1815a.log', 'SourceOriginalResidueCuspBaseComparison-1830.exit', 'SourceOriginalResidueCuspBaseComparison-1830.log', 'SourceOriginalResidueCuspBaseComparison.lean', 'SourceOriginalResidueCuspBaseComparison1822a.exit', 'SourceOriginalResidueCuspBaseComparison1822a.lean', 'SourceOriginalResidueCuspBaseComparison1822a.log', 'SourceOriginalResidueCuspCount-1845.exit', 'SourceOriginalResidueCuspCount-1845.log', 'SourceOriginalResidueCuspCount.lean', 'SourceOriginalResidueCuspCount1843a.exit', 'SourceOriginalResidueCuspCount1843a.lean', 'SourceOriginalResidueCuspCount1843a.log', 'SourceOriginalResidueCuspCountAudit1.exit', 'SourceOriginalResidueCuspCountAudit1.lean', 'SourceOriginalResidueCuspCountAudit1.log', 'SourceOriginalResidueCuspCountAudit2.exit', 'SourceOriginalResidueCuspCountAudit2.lean', 'SourceOriginalResidueCuspCountAudit2.log', 'SourceOriginalResidueCuspCountDependencyAudit1.exit', 'SourceOriginalResidueCuspCountDependencyAudit1.lean', 'SourceOriginalResidueCuspCountDependencyAudit1.log', 'SourceOriginalResidueCuspCountDependencyAudit2.exit', 'SourceOriginalResidueCuspCountDependencyAudit2.lean', 'SourceOriginalResidueCuspCountDependencyAudit2.log', 'SourceOriginalResidueCuspCountScratchOwnership1850.exit', 'SourceOriginalResidueCuspCountScratchOwnership1850.lean', 'SourceOriginalResidueCuspCountScratchOwnership1850.log', 'SourceOriginalResidueCuspFamilyBaseLabel-1845.exit', 'SourceOriginalResidueCuspFamilyBaseLabel-1845.log', 'SourceOriginalResidueCuspFamilyBaseLabel.lean', 'SourceOriginalResidueCuspFamilyBaseLabel1840a.exit', 'SourceOriginalResidueCuspFamilyBaseLabel1840a.lean', 'SourceOriginalResidueCuspFamilyBaseLabel1840a.log', 'SourceOriginalResidueCuspFamilyExhaustion-1845.exit', 'SourceOriginalResidueCuspFamilyExhaustion-1845.log', 'SourceOriginalResidueCuspFamilyExhaustion.lean', 'SourceOriginalResidueCuspFamilyExhaustion1841a.exit', 'SourceOriginalResidueCuspFamilyExhaustion1841a.lean', 'SourceOriginalResidueCuspFamilyExhaustion1841a.log', 'SourceOriginalResidueCuspFiberAudit1.exit', 'SourceOriginalResidueCuspFiberAudit1.lean', 'SourceOriginalResidueCuspFiberAudit1.log', 'SourceOriginalResidueCuspFiberDependencyAudit1.exit', 'SourceOriginalResidueCuspFiberDependencyAudit1.lean', 'SourceOriginalResidueCuspFiberDependencyAudit1.log', 'SourceOriginalResidueCuspFiberScratchOwnership1844.exit', 'SourceOriginalResidueCuspFiberScratchOwnership1844.lean', 'SourceOriginalResidueCuspFiberScratchOwnership1844.log', 'SourceOriginalResidueCuspHomFamily-1845.exit', 'SourceOriginalResidueCuspHomFamily-1845.log', 'SourceOriginalResidueCuspHomFamily.lean', 'SourceOriginalResidueCuspHomFamily1832a.exit', 'SourceOriginalResidueCuspHomFamily1832a.lean', 'SourceOriginalResidueCuspHomFamily1832a.log', 'SourceOriginalResidueCuspMatrix-1830.exit', 'SourceOriginalResidueCuspMatrix-1830.log', 'SourceOriginalResidueCuspMatrix.lean', 'SourceOriginalResidueCuspMatrix1824a.exit', 'SourceOriginalResidueCuspMatrix1824a.lean.txt', 'SourceOriginalResidueCuspMatrix1824a.log', 'SourceOriginalResidueCuspMatrix1824b.exit', 'SourceOriginalResidueCuspMatrix1824b.lean', 'SourceOriginalResidueCuspMatrix1824b.log', 'SourceOriginalResidueCuspOrbitMap-1845.exit', 'SourceOriginalResidueCuspOrbitMap-1845.log', 'SourceOriginalResidueCuspOrbitMap.lean', 'SourceOriginalResidueCuspOrbitMap1837a.exit', 'SourceOriginalResidueCuspOrbitMap1837a.lean', 'SourceOriginalResidueCuspOrbitMap1837a.log', 'SourceOriginalResidueCuspOrbitSurjection-1845.exit', 'SourceOriginalResidueCuspOrbitSurjection-1845.log', 'SourceOriginalResidueCuspOrbitSurjection.lean', 'SourceOriginalResidueCuspOrbitSurjection1842a.exit', 'SourceOriginalResidueCuspOrbitSurjection1842a.lean.txt', 'SourceOriginalResidueCuspOrbitSurjection1842a.log', 'SourceOriginalResidueCuspOrbitSurjection1842b.exit', 'SourceOriginalResidueCuspOrbitSurjection1842b.lean.txt', 'SourceOriginalResidueCuspOrbitSurjection1842b.log', 'SourceOriginalResidueCuspOrbitSurjection1842c.exit', 'SourceOriginalResidueCuspOrbitSurjection1842c.lean', 'SourceOriginalResidueCuspOrbitSurjection1842c.log', 'SourceOriginalResidueCuspPlaceCovariance-1845.exit', 'SourceOriginalResidueCuspPlaceCovariance-1845.log', 'SourceOriginalResidueCuspPlaceCovariance.lean', 'SourceOriginalResidueCuspPlaceCovariance1835a.exit', 'SourceOriginalResidueCuspPlaceCovariance1835a.lean', 'SourceOriginalResidueCuspPlaceCovariance1835a.log', 'SourceOriginalResidueCuspPlaceFamily-1845.exit', 'SourceOriginalResidueCuspPlaceFamily-1845.log', 'SourceOriginalResidueCuspPlaceFamily.lean', 'SourceOriginalResidueCuspPlaceFamily1833a.exit', 'SourceOriginalResidueCuspPlaceFamily1833a.lean.txt', 'SourceOriginalResidueCuspPlaceFamily1833a.log', 'SourceOriginalResidueCuspPlaceFamily1833b.exit', 'SourceOriginalResidueCuspPlaceFamily1833b.lean', 'SourceOriginalResidueCuspPlaceFamily1833b.log', 'SourceOriginalResidueCuspPlaceOverBase-1830.exit', 'SourceOriginalResidueCuspPlaceOverBase-1830.log', 'SourceOriginalResidueCuspPlaceOverBase.lean', 'SourceOriginalResidueCuspPlaceOverBase1823a.exit', 'SourceOriginalResidueCuspPlaceOverBase1823a.lean.txt', 'SourceOriginalResidueCuspPlaceOverBase1823a.log', 'SourceOriginalResidueCuspPlaceOverBase1823b.exit', 'SourceOriginalResidueCuspPlaceOverBase1823b.lean', 'SourceOriginalResidueCuspPlaceOverBase1823b.log', 'SourceOriginalResidueCuspStabilizerPlace-1813.exit', 'SourceOriginalResidueCuspStabilizerPlace-1813.log', 'SourceOriginalResidueCuspStabilizerPlace.lean', 'SourceOriginalResidueCuspStabilizerPlace1807a.exit', 'SourceOriginalResidueCuspStabilizerPlace1807a.lean', 'SourceOriginalResidueCuspStabilizerPlace1807a.log', 'SourceOriginalResidueCuspStabilizerPlace1807b.exit', 'SourceOriginalResidueCuspStabilizerPlace1807b.lean', 'SourceOriginalResidueCuspStabilizerPlace1807b.log', 'SourceOriginalResidueDiamondCommute-1844.exit', 'SourceOriginalResidueDiamondCommute-1844.log', 'SourceOriginalResidueDiamondCommute.lean', 'SourceOriginalResidueDiamondCommute1827a.exit', 'SourceOriginalResidueDiamondCommute1827a.lean', 'SourceOriginalResidueDiamondCommute1827a.log', 'SourceOriginalResidueDiamondCuspChart-1813.exit', 'SourceOriginalResidueDiamondCuspChart-1813.log', 'SourceOriginalResidueDiamondCuspChart.lean', 'SourceOriginalResidueDiamondCuspChart1806a.exit', 'SourceOriginalResidueDiamondCuspChart1806a.lean', 'SourceOriginalResidueDiamondCuspChart1806a.log', 'SourceOriginalResidueDiamondFiberStabilizer-1844.exit', 'SourceOriginalResidueDiamondFiberStabilizer-1844.log', 'SourceOriginalResidueDiamondFiberStabilizer.lean', 'SourceOriginalResidueDiamondFiberStabilizer1828a.exit', 'SourceOriginalResidueDiamondFiberStabilizer1828a.lean.txt', 'SourceOriginalResidueDiamondFiberStabilizer1828a.log', 'SourceOriginalResidueDiamondFiberStabilizer1828b.exit', 'SourceOriginalResidueDiamondFiberStabilizer1828b.lean', 'SourceOriginalResidueDiamondFiberStabilizer1828b.log', 'SourceOriginalResidueFullBaseFinite-1845.exit', 'SourceOriginalResidueFullBaseFinite-1845.log', 'SourceOriginalResidueFullBaseFinite.lean', 'SourceOriginalResidueFullBaseFinite1838a.exit', 'SourceOriginalResidueFullBaseFinite1838a.lean.txt', 'SourceOriginalResidueFullBaseFinite1838a.log', 'SourceOriginalResidueFullBaseFinite1838b.exit', 'SourceOriginalResidueFullBaseFinite1838b.lean', 'SourceOriginalResidueFullBaseFinite1838b.log', 'SourceOriginalResidueFullCuspChart-1830.exit', 'SourceOriginalResidueFullCuspChart-1830.log', 'SourceOriginalResidueFullCuspChart.lean', 'SourceOriginalResidueFullCuspChart1821a.exit', 'SourceOriginalResidueFullCuspChart1821a.lean', 'SourceOriginalResidueFullCuspChart1821a.log', 'SourceOriginalResidueImageCuspCount-1850.exit', 'SourceOriginalResidueImageCuspCount-1850.log', 'SourceOriginalResidueImageCuspCount.lean', 'SourceOriginalResidueImageCuspCount1847a.exit', 'SourceOriginalResidueImageCuspCount1847a.lean.txt', 'SourceOriginalResidueImageCuspCount1847a.log', 'SourceOriginalResidueImageCuspCount1847b.exit', 'SourceOriginalResidueImageCuspCount1847b.lean', 'SourceOriginalResidueImageCuspCount1847b.log', 'SourceOriginalResidueLabeledCuspAudit1.exit', 'SourceOriginalResidueLabeledCuspAudit1.lean', 'SourceOriginalResidueLabeledCuspAudit1.log', 'SourceOriginalResidueLabeledCuspDependencyAudit1.exit', 'SourceOriginalResidueLabeledCuspDependencyAudit1.lean', 'SourceOriginalResidueLabeledCuspDependencyAudit1.log', 'SourceOriginalResidueLabeledCuspFiber-1844.exit', 'SourceOriginalResidueLabeledCuspFiber-1844.log', 'SourceOriginalResidueLabeledCuspFiber.lean', 'SourceOriginalResidueLabeledCuspFiber1829a.exit', 'SourceOriginalResidueLabeledCuspFiber1829a.lean', 'SourceOriginalResidueLabeledCuspFiber1829a.log', 'SourceOriginalResidueLabeledCuspPlace-1830.exit', 'SourceOriginalResidueLabeledCuspPlace-1830.log', 'SourceOriginalResidueLabeledCuspPlace.lean', 'SourceOriginalResidueLabeledCuspPlace1825a.exit', 'SourceOriginalResidueLabeledCuspPlace1825a.lean', 'SourceOriginalResidueLabeledCuspPlace1825a.log', 'SourceOriginalResidueLabeledCuspScratchOwnership1830.exit', 'SourceOriginalResidueLabeledCuspScratchOwnership1830.lean', 'SourceOriginalResidueLabeledCuspScratchOwnership1830.log', 'SourceOriginalResiduePoleBaseLabel-1845.exit', 'SourceOriginalResiduePoleBaseLabel-1845.log', 'SourceOriginalResiduePoleBaseLabel.lean', 'SourceOriginalResiduePoleBaseLabel1839a.exit', 'SourceOriginalResiduePoleBaseLabel1839a.lean.txt', 'SourceOriginalResiduePoleBaseLabel1839a.log', 'SourceOriginalResiduePoleBaseLabel1839b.exit', 'SourceOriginalResiduePoleBaseLabel1839b.lean', 'SourceOriginalResiduePoleBaseLabel1839b.log', 'anthropic-diamond-place-charts-1746/manifest.json', 'anthropic-original-residue-charts-1750/manifest.json', 'audit_actual_residue_cusp_stabilizer_1813.ps1', 'audit_actual_residue_cusp_stabilizer_preflight_1810.ps1', 'audit_original_residue_cusp_count_1845.ps1', 'audit_original_residue_cusp_count_1850.ps1', 'audit_original_residue_cusp_fiber_1844.ps1', 'audit_original_residue_cusp_fiber_preflight_1834.ps1', 'audit_original_residue_cusp_fiber_preflight_1836.ps1', 'audit_original_residue_labeled_cusp_1830.ps1', 'audit_original_residue_labeled_cusp_preflight_1826.ps1', 'build_actual_residue_cusp_stabilizer_canonical_1813.ps1', 'build_original_residue_cusp_count_canonical_1845.ps1', 'build_original_residue_cusp_count_canonical_1850.ps1', 'build_original_residue_cusp_fiber_canonical_1844.ps1', 'build_original_residue_labeled_cusp_canonical_1830.ps1', 'original-residue-cusp-bounds-promotion-route-1854.json', 'original-residue-cusp-orbit-route-1831.json', 'prepare_actual_residue_cusp_stabilizer_canonical_1813.py', 'record_actual_residue_cusp_stabilizer_1813.py', 'record_original_residue_cusp_count_1845.py', 'record_original_residue_cusp_count_1850.py', 'record_original_residue_cusp_fiber_1844.py', 'record_original_residue_labeled_cusp_1830.py', 'source-actual-residue-cusp-stabilizer-1-audit-config.json', 'source-actual-residue-cusp-stabilizer-1-reuse-review-20261029.json', 'source-actual-residue-cusp-stabilizer-1-scratch-receipt.json', 'source-actual-residue-cusp-stabilizer-audit-route-1813.json', 'source-original-residue-cusp-count-2-audit-config.json', 'source-original-residue-cusp-count-2-reuse-review-20261029.json', 'source-original-residue-cusp-count-2-scratch-receipt.json', 'source-original-residue-cusp-count-audit-route-1850.json', 'source-original-residue-cusp-fiber-1-audit-config.json', 'source-original-residue-cusp-fiber-1-reuse-review-20261029.json', 'source-original-residue-cusp-fiber-1-scratch-receipt.json', 'source-original-residue-cusp-fiber-audit-route-1844.json', 'source-original-residue-fixed-fibers-1-scratch-receipt.json', 'source-original-residue-labeled-cusp-1-audit-config.json', 'source-original-residue-labeled-cusp-1-reuse-review-20261029.json', 'source-original-residue-labeled-cusp-1-scratch-receipt.json', 'source-original-residue-labeled-cusp-audit-route-1830.json', 'source-prescribed-residue-cusp-chart-1-scratch-receipt.json', 'source-reduced-cusp-translation-1-scratch-receipt.json', 'source-reduced-diamond-scalar-1-scratch-receipt.json']]
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
supplemental_review_path=r/archive_rel/'original-residue-cusp-bounds-promotion-route-1854.json'

for name in ['Dubon Actual Residue Cusp Stabilizer Assessment 2026-10-29.md', 'Dubon Original Residue Labeled Cusp Assessment 2026-10-29.md', 'Dubon Original Residue Cusp Fiber Assessment 2026-10-29.md', 'Dubon Original Residue Cusp Count Assessment 2026-10-29.md']:
    target=r/name
    assert not target.exists(),target
    refresh_pending.append((target,(p/name).read_bytes(),'root'))

audit = r / "Extension/Dubon2026/Audit.lean"
at = audit.read_text(encoding="utf-8")
for n in queries:
    assert not re.search(r"``" + re.escape(n) + r"(?=[,\s])", at)
tm, dm = "\n]\n\nprivate def publicConstructions", "\n]\n\nprivate def runAudit"
assert at.count(tm) == at.count(dm) == 1
at = at.replace(tm, "".join("\n  ,``" + n for n in theorems) + tm, 1)
at = at.replace(dm, "".join("\n  ," + chr(96)*2 + n for n in defs) + dm, 1)
research_path = r / "Tools/lean-reuse-audit-20261020.json"
reuse_path = r / "Tools/source-original-residue-cusp-bounds.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt9374"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> automorphy -> original all-weight characteristic-zero association -> actual homogeneous Gamma1 Hecke-character realization -> original genus preservation -> reverse genus inequality -> residue cusp and finite elliptic fiber bounds.'
discharged = 'The actual residue diamond action is identified with the constructed cusp embedding on the whole original function field. Both j and j_N have their exact source Laurent coordinates in the same chart. Every native primitive cusp label has a constructed matrix and an actual place above it. The actual diamond action is commutative, and signed-translation stabilizers fix the entire corresponding base fiber. A single coefficient reduction gives a cusp-place family on the existing signed Gamma1 cosets and translation orbits. Native full-base cusp exhaustion and actual diamond transitivity prove that this orbit map covers every residue j-pole. The native complex cusp-orbit bijection therefore proves that the actual residue cusp count is at most the complex cusp count, for every prime away from the level, including 2 and 3. The primitive root and coefficient reduction are constructed. The proved field equality transports this bound to the literal coefficient residue image and its native j coordinate. No chart, action, transitivity, degree, field-identification or cusp-count certificate remains in the final residue-image cusp-count theorem.'
boundary = 'Finite elliptic charts and finite fiber bounds, including residue characteristics two and three, and the reverse genus inequality remain open. Original genus preservation, integral parabolic transfer, exceptional-prime removal, two-dimensional characteristic-zero realization, original all-weight association, remaining local/image/regularity inputs, automorphy and literal higher continuation remain required. Acceptance stays 16/20; DUB-17--20 OPEN; every original source and verification criterion is unchanged.'
status = 'The 36-module scratch scope passes 57 public axiom queries, 138 exhaustive theorem checks, sixteen linters per module and four declaration-value audits with 100 required dependencies, with zero diagnostics. Production aggregate, focused audits and sequential foundation/paper verification of the 9,410-module scope are pending.'
route = 'The October 29 reuse refresh is applied to the exact unresolved source chain. Native normalized-generator extension proves full-field diamond covariance. Native Fourier coefficient uniqueness and sparse power-series expansion replace a new analytic coset framework for j_N. The native coprime-lift and SL2 row-completion lemmas construct cusp matrices. Native exact-kernel and Galois place-transitivity proofs give all-fiber stabilizers. The existing complex signed-coset translation orbits provide a shorter residue cusp surjection proof than the external generic double-coset injection. Four scopes are promoted by import qualification only; all mathematical statements, bodies and comments are frozen. All public/private/generated axiom checks, sixteen linters per module, all 100 required VALUE dependencies, exact ownership and sequential foundation/paper verification remain mandatory. Frozen paper, root pins and owner-only BAT are unchanged. Historical scope reports retain their original boundaries; the current combined status supersedes them.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Original residue cusp bounds (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 9,374-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
corrections = []
count = sum(z['exhaustiveTheorems'] for z in certs)
assert count == 138

docpaths = list(dict.fromkeys(r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]))
for f in docpaths:
    assert "\n\n" in f.read_text(encoding="utf-8")
readmes = [(r.parent / "README.md", "Current Project 83 status ("), (repo / "README.md", "Project 83 has an ")]
for f, prefix in readmes:
    assert sum(line.startswith(prefix) for line in f.read_text(encoding="utf-8").splitlines()) == 1
arch = r / "Dubon Architecture.md"
edge = '  RESIDUECHART9374["Actual residue diamond action, full-base fixed field, orbit transitivity and prescribed cusp field charts proved. Diamond equivariance, fiber bounds, reverse genus and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourceOriginalResidueCuspBoundsProductionAudit9410.lean',p/'source-original-residue-cusp-bounds-9410-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production9410.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/original-residue-cusp-charts-20261029-1800'
registered = {row['path'] for row in c['files']}
for priorFile in priorArchive.iterdir():
    rel = priorFile.relative_to(r).as_posix()
    if priorFile.is_file() and rel not in registered:
        c['files'].append({'path': rel, 'role': 'Tools'})

reportSource = p / 'Dubon Original Residue Cusp Bounds Assessment 2026-10-29.md'
assert sha(reportSource) == '911125DE9B906FAA298CEBC6560B9E044A6833DB344A00179557CA1049D83DC0'
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
    "productionModules": 9410, "modules": newmods, "queries": queries,
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
arch.write_text(arch.read_text(encoding='utf-8').replace(edge,'  RESIDUECHART9374["Actual residue diamond action, full-base fixed field, orbit transitivity and cusp charts proved (DUB-17/18)"] --> CUSPBOUND9410\n  CUSPBOUND9410["Full-field diamond covariance, exact j/j_N cusp charts, all-fiber cusp stabilizers and actual residue-image cusp upper count proved. Finite elliptic fiber bounds, reverse genus and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'),encoding='utf-8')



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Original residue cusp bounds - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-original-residue-cusp-bounds.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub('  logInfo m!".*"\n', '  logInfo m!"SOURCE ORIGINAL RESIDUE CUSP BOUNDS AUDIT PASS: {count} theorems including private/generated declarations. Actual diamond-equivariant j/j_N charts and residue-image cusp count proved. Finite elliptic bounds, reverse genus and source gates OPEN;16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourceOriginalResidueCuspBoundsProductionAudit9410.lean").write_text(out, encoding="utf-8")
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
    target = p / (source.stem + "Production9410.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
(p / "source-original-residue-cusp-bounds-9410-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 9410, "increment": 36, "queries": 57,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
