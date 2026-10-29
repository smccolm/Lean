from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 9410
assert d["appliedSourceOriginalResidueCuspBounds"]["receipt9410"]["exit"] == 0
assert (p / "paper-verification-9410-console.exit").read_text().strip() == "0"
assert (r/'Tools/original-residue-cusp-bounds-20261029-1854/canonical-evidence-9410.json').exists()
key = "appliedSourceToricMarkedPoint"
assert key not in d
digests = {'source-integral-toric-forms-2-scratch-receipt.json': '859483F6B6AD8B4D6A49C4D8EB66F0036320A8A45876F48372C948308CC7AF48', 'source-original-toric-coordinates-3-scratch-receipt.json': '53E6CD3C2893482A517D2543E7ADF6AF366AB2EDE0F388B122FEA90B0B28890E', 'source-toric-marked-point-1-scratch-receipt.json': '990FB59357224BD399D983D7A78C89DA64905CBEAAAA361A74CED8E9316763BE'}

for name, digest in digests.items():
    assert sha(p / name) == digest
certs = [json.loads((p / name).read_text(encoding="utf-8")) for name in digests]
mods = [m for z in certs for m in z["modules"]]
queries = [q for z in certs for q in z["queries"]]
theorems = [q for z in certs for q in z["theoremRegistrations"]]
defs = [q for z in certs for q in z["constructionRegistrations"]]
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (40, 40, 220, 163, 57)
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
archive_rel='Tools/toric-marked-point-20261029-1901'
evidence=[p/n for n in ['Dubon Toric Marked Point Assessment 2026-10-29.md', 'SourceGammaOneDivisionCoefficientFibers-1872.exit', 'SourceGammaOneDivisionCoefficientFibers-1872.log', 'SourceGammaOneDivisionCoefficientFibers.lean', 'SourceGammaOneDivisionDivisorCoefficients-1872.exit', 'SourceGammaOneDivisionDivisorCoefficients-1872.log', 'SourceGammaOneDivisionDivisorCoefficients.lean', 'SourceGammaOneDivisionFourier-1872.exit', 'SourceGammaOneDivisionFourier-1872.log', 'SourceGammaOneDivisionFourier.lean', 'SourceGammaOneDivisionToricForms-1872.exit', 'SourceGammaOneDivisionToricForms-1872.log', 'SourceGammaOneDivisionToricForms.lean', 'SourceGammaOneDivisionToricForms1871a.exit', 'SourceGammaOneDivisionToricForms1871a.lean', 'SourceGammaOneDivisionToricForms1871a.log', 'SourceGammaOneIntegralToricForms-1872.exit', 'SourceGammaOneIntegralToricForms-1872.log', 'SourceGammaOneIntegralToricForms.lean', 'SourceGammaOneIntegralToricReconstruction-1872.exit', 'SourceGammaOneIntegralToricReconstruction-1872.log', 'SourceGammaOneIntegralToricReconstruction.lean', 'SourceGammaOneIntegralToricSlash-1872.exit', 'SourceGammaOneIntegralToricSlash-1872.log', 'SourceGammaOneIntegralToricSlash.lean', 'SourceGammaOneIntegralToricWeightFour-1872.exit', 'SourceGammaOneIntegralToricWeightFour-1872.log', 'SourceGammaOneIntegralToricWeightFour.lean', 'SourceGammaOneIntegralToricWeightTwo-1872.exit', 'SourceGammaOneIntegralToricWeightTwo-1872.log', 'SourceGammaOneIntegralToricWeightTwo.lean', 'SourceGammaOneNormalizedDivisionForm-1872.exit', 'SourceGammaOneNormalizedDivisionForm-1872.log', 'SourceGammaOneNormalizedDivisionForm.lean', 'SourceGammaOneOriginalToricCoordinates-1883.exit', 'SourceGammaOneOriginalToricCoordinates-1883.log', 'SourceGammaOneOriginalToricCoordinates.lean', 'SourceGammaOneOriginalToricCoordinates1882a.exit', 'SourceGammaOneOriginalToricCoordinates1882a.lean', 'SourceGammaOneOriginalToricCoordinates1882a.log', 'SourceGammaOneToricCoordinateDiamond-1883.exit', 'SourceGammaOneToricCoordinateDiamond-1883.log', 'SourceGammaOneToricCoordinateDiamond.lean', 'SourceGammaOneToricCoordinateDiamond1881a.exit', 'SourceGammaOneToricCoordinateDiamond1881a.lean.txt', 'SourceGammaOneToricCoordinateDiamond1881a.log', 'SourceGammaOneToricCoordinateDiamond1881b.exit', 'SourceGammaOneToricCoordinateDiamond1881b.lean', 'SourceGammaOneToricCoordinateDiamond1881b.log', 'SourceGammaOneToricOriginalCoordinateValues-1883.exit', 'SourceGammaOneToricOriginalCoordinateValues-1883.log', 'SourceGammaOneToricOriginalCoordinateValues.lean', 'SourceGammaOneToricOriginalCoordinateValues1878a.exit', 'SourceGammaOneToricOriginalCoordinateValues1878a.lean.txt', 'SourceGammaOneToricOriginalCoordinateValues1878a.log', 'SourceGammaOneToricOriginalCoordinateValues1878b.exit', 'SourceGammaOneToricOriginalCoordinateValues1878b.lean', 'SourceGammaOneToricOriginalCoordinateValues1878b.log', 'SourceGammaOneToricOriginalCoordinates-1883.exit', 'SourceGammaOneToricOriginalCoordinates-1883.log', 'SourceGammaOneToricOriginalCoordinates.lean', 'SourceGammaOneToricOriginalCoordinates1877a.exit', 'SourceGammaOneToricOriginalCoordinates1877a.lean', 'SourceGammaOneToricOriginalCoordinates1877a.log', 'SourceGammaOneToricOriginalRatios-1883.exit', 'SourceGammaOneToricOriginalRatios-1883.log', 'SourceGammaOneToricOriginalRatios.lean', 'SourceGammaOneToricOriginalRatios1876a.exit', 'SourceGammaOneToricOriginalRatios1876a.lean', 'SourceGammaOneToricOriginalRatios1876a.log', 'SourceGammaOneToricRatioDiamond-1883.exit', 'SourceGammaOneToricRatioDiamond-1883.log', 'SourceGammaOneToricRatioDiamond.lean', 'SourceGammaOneToricRatioDiamond1880a.exit', 'SourceGammaOneToricRatioDiamond1880a.lean', 'SourceGammaOneToricRatioDiamond1880a.log', 'SourceIntegralDiamondScalarRatioAction-1883.exit', 'SourceIntegralDiamondScalarRatioAction-1883.log', 'SourceIntegralDiamondScalarRatioAction.lean', 'SourceIntegralDiamondScalarRatioAction1879a.exit', 'SourceIntegralDiamondScalarRatioAction1879a.lean', 'SourceIntegralDiamondScalarRatioAction1879a.log', 'SourceIntegralToricFormsAudit1.exit', 'SourceIntegralToricFormsAudit1.lean.txt', 'SourceIntegralToricFormsAudit1.log', 'SourceIntegralToricFormsAudit2.exit', 'SourceIntegralToricFormsAudit2.lean', 'SourceIntegralToricFormsAudit2.log', 'SourceIntegralToricFormsDependencyAudit1.lean', 'SourceIntegralToricFormsDependencyAudit2.exit', 'SourceIntegralToricFormsDependencyAudit2.lean', 'SourceIntegralToricFormsDependencyAudit2.log', 'SourceIntegralToricFormsScratchOwnership1872.exit', 'SourceIntegralToricFormsScratchOwnership1872.lean', 'SourceIntegralToricFormsScratchOwnership1872.log', 'SourceOriginalToricCoordinatesAudit1.exit', 'SourceOriginalToricCoordinatesAudit1.lean.txt', 'SourceOriginalToricCoordinatesAudit1.log', 'SourceOriginalToricCoordinatesAudit2.exit', 'SourceOriginalToricCoordinatesAudit2.lean', 'SourceOriginalToricCoordinatesAudit2.log', 'SourceOriginalToricCoordinatesDependencyAudit1.exit', 'SourceOriginalToricCoordinatesDependencyAudit1.lean.txt', 'SourceOriginalToricCoordinatesDependencyAudit1.log', 'SourceOriginalToricCoordinatesDependencyAudit2.exit', 'SourceOriginalToricCoordinatesDependencyAudit2.lean', 'SourceOriginalToricCoordinatesDependencyAudit2.log', 'SourceOriginalToricCoordinatesScratchOwnership1883.exit', 'SourceOriginalToricCoordinatesScratchOwnership1883.lean', 'SourceOriginalToricCoordinatesScratchOwnership1883.log', 'SourceTateA4Series-1872.exit', 'SourceTateA4Series-1872.log', 'SourceTateA4Series.lean', 'SourceTateCoefficientNormalization-1899.exit', 'SourceTateCoefficientNormalization-1899.log', 'SourceTateCoefficientNormalization.lean', 'SourceTateCoefficientNormalization1889a.exit', 'SourceTateCoefficientNormalization1889a.lean', 'SourceTateCoefficientNormalization1889a.log', 'SourceTateEisensteinInvariants-1883.exit', 'SourceTateEisensteinInvariants-1883.log', 'SourceTateEisensteinInvariants.lean', 'SourceTateEisensteinInvariants1875a.exit', 'SourceTateEisensteinInvariants1875a.lean.txt', 'SourceTateEisensteinInvariants1875a.log', 'SourceTateEisensteinInvariants1875b.exit', 'SourceTateEisensteinInvariants1875b.lean', 'SourceTateEisensteinInvariants1875b.log', 'SourceTateIntegralCoefficients-1883.exit', 'SourceTateIntegralCoefficients-1883.log', 'SourceTateIntegralCoefficients.lean', 'SourceTateIntegralCoefficients1873a.exit', 'SourceTateIntegralCoefficients1873a.lean', 'SourceTateIntegralCoefficients1873a.log', 'SourceTateIntegralCurve-1883.exit', 'SourceTateIntegralCurve-1883.log', 'SourceTateIntegralCurve.lean', 'SourceTateIntegralCurve1874a.exit', 'SourceTateIntegralCurve1874a.lean', 'SourceTateIntegralCurve1874a.log', 'SourceToricAnalyticCurve-1899.exit', 'SourceToricAnalyticCurve-1899.log', 'SourceToricAnalyticCurve.lean', 'SourceToricAnalyticCurve1884a.exit', 'SourceToricAnalyticCurve1884a.lean.txt', 'SourceToricAnalyticCurve1884a.log', 'SourceToricAnalyticCurve1884b.exit', 'SourceToricAnalyticCurve1884b.lean.txt', 'SourceToricAnalyticCurve1884b.log', 'SourceToricAnalyticCurve1884c.exit', 'SourceToricAnalyticCurve1884c.lean', 'SourceToricAnalyticCurve1884c.log', 'SourceToricAnalyticDivisionRoot-1899.exit', 'SourceToricAnalyticDivisionRoot-1899.log', 'SourceToricAnalyticDivisionRoot.lean', 'SourceToricAnalyticDivisionRoot1886a.exit', 'SourceToricAnalyticDivisionRoot1886a.lean.txt', 'SourceToricAnalyticDivisionRoot1886a.log', 'SourceToricAnalyticDivisionRoot1886b.exit', 'SourceToricAnalyticDivisionRoot1886b.lean', 'SourceToricAnalyticDivisionRoot1886b.log', 'SourceToricAnalyticMultiplication-1899.exit', 'SourceToricAnalyticMultiplication-1899.log', 'SourceToricAnalyticMultiplication.lean', 'SourceToricAnalyticMultiplication1894a.exit', 'SourceToricAnalyticMultiplication1894a.lean', 'SourceToricAnalyticMultiplication1894a.log', 'SourceToricAnalyticTorsion-1899.exit', 'SourceToricAnalyticTorsion-1899.log', 'SourceToricAnalyticTorsion.lean', 'SourceToricAnalyticTorsion1885a.exit', 'SourceToricAnalyticTorsion1885a.lean', 'SourceToricAnalyticTorsion1885a.log', 'SourceToricCoefficientLocalization-1899.exit', 'SourceToricCoefficientLocalization-1899.log', 'SourceToricCoefficientLocalization.lean', 'SourceToricCoefficientLocalization1891a.exit', 'SourceToricCoefficientLocalization1891a.lean', 'SourceToricCoefficientLocalization1891a.log', 'SourceToricComplexSeriesDivision-1899.exit', 'SourceToricComplexSeriesDivision-1899.log', 'SourceToricComplexSeriesDivision.lean', 'SourceToricComplexSeriesDivision1890a.exit', 'SourceToricComplexSeriesDivision1890a.lean.txt', 'SourceToricComplexSeriesDivision1890a.log', 'SourceToricComplexSeriesDivision1890b.exit', 'SourceToricComplexSeriesDivision1890b.lean', 'SourceToricComplexSeriesDivision1890b.log', 'SourceToricCuspDivisionIdentity-1899.exit', 'SourceToricCuspDivisionIdentity-1899.log', 'SourceToricCuspDivisionIdentity.lean', 'SourceToricCuspDivisionIdentity1888a.exit', 'SourceToricCuspDivisionIdentity1888a.lean.txt', 'SourceToricCuspDivisionIdentity1888a.log', 'SourceToricCuspDivisionIdentity1888b.exit', 'SourceToricCuspDivisionIdentity1888b.lean', 'SourceToricCuspDivisionIdentity1888b.log', 'SourceToricCuspExpansionHom-1899.exit', 'SourceToricCuspExpansionHom-1899.log', 'SourceToricCuspExpansionHom.lean', 'SourceToricCuspExpansionHom1887a.exit', 'SourceToricCuspExpansionHom1887a.lean.txt', 'SourceToricCuspExpansionHom1887a.log', 'SourceToricCuspExpansionHom1887b.exit', 'SourceToricCuspExpansionHom1887b.lean', 'SourceToricCuspExpansionHom1887b.log', 'SourceToricExactOrderPoint-1899.exit', 'SourceToricExactOrderPoint-1899.log', 'SourceToricExactOrderPoint.lean', 'SourceToricExactOrderPoint1897a.exit', 'SourceToricExactOrderPoint1897a.lean.txt', 'SourceToricExactOrderPoint1897a.log', 'SourceToricExactOrderPoint1897b.exit', 'SourceToricExactOrderPoint1897b.lean.txt', 'SourceToricExactOrderPoint1897b.log', 'SourceToricExactOrderPoint1897c.exit', 'SourceToricExactOrderPoint1897c.lean', 'SourceToricExactOrderPoint1897c.log', 'SourceToricFieldDivisionIdentities-1899.exit', 'SourceToricFieldDivisionIdentities-1899.log', 'SourceToricFieldDivisionIdentities.lean', 'SourceToricFieldDivisionIdentities1896a.exit', 'SourceToricFieldDivisionIdentities1896a.lean.txt', 'SourceToricFieldDivisionIdentities1896a.log', 'SourceToricFieldDivisionIdentities1896b.exit', 'SourceToricFieldDivisionIdentities1896b.lean', 'SourceToricFieldDivisionIdentities1896b.log', 'SourceToricFourierCharacters-1872.exit', 'SourceToricFourierCharacters-1872.log', 'SourceToricFourierCharacters.lean', 'SourceToricIntegerCoefficientFamilies-1872.exit', 'SourceToricIntegerCoefficientFamilies-1872.log', 'SourceToricIntegerCoefficientFamilies.lean', 'SourceToricIntegerFourierTransform-1872.exit', 'SourceToricIntegerFourierTransform-1872.log', 'SourceToricIntegerFourierTransform.lean', 'SourceToricIntegralCoefficientPolynomials-1872.exit', 'SourceToricIntegralCoefficientPolynomials-1872.log', 'SourceToricIntegralCoefficientPolynomials.lean', 'SourceToricLocalizedSeries-1899.exit', 'SourceToricLocalizedSeries-1899.log', 'SourceToricLocalizedSeries.lean', 'SourceToricLocalizedSeries1892a.exit', 'SourceToricLocalizedSeries1892a.lean', 'SourceToricLocalizedSeries1892a.log', 'SourceToricMarkedPointAudit1.exit', 'SourceToricMarkedPointAudit1.lean', 'SourceToricMarkedPointAudit1.log', 'SourceToricMarkedPointCoordinates-1899.exit', 'SourceToricMarkedPointCoordinates-1899.log', 'SourceToricMarkedPointCoordinates.lean', 'SourceToricMarkedPointCoordinates1898a.exit', 'SourceToricMarkedPointCoordinates1898a.lean.txt', 'SourceToricMarkedPointCoordinates1898a.log', 'SourceToricMarkedPointCoordinates1898b.exit', 'SourceToricMarkedPointCoordinates1898b.lean.txt', 'SourceToricMarkedPointCoordinates1898b.log', 'SourceToricMarkedPointCoordinates1898c.exit', 'SourceToricMarkedPointCoordinates1898c.lean', 'SourceToricMarkedPointCoordinates1898c.log', 'SourceToricMarkedPointDependencyAudit1.exit', 'SourceToricMarkedPointDependencyAudit1.lean', 'SourceToricMarkedPointDependencyAudit1.log', 'SourceToricMarkedPointScratchOwnership1899.exit', 'SourceToricMarkedPointScratchOwnership1899.lean', 'SourceToricMarkedPointScratchOwnership1899.log', 'SourceToricResidueDivisionIdentity-1899.exit', 'SourceToricResidueDivisionIdentity-1899.log', 'SourceToricResidueDivisionIdentity.lean', 'SourceToricResidueDivisionIdentity1893a.exit', 'SourceToricResidueDivisionIdentity1893a.lean', 'SourceToricResidueDivisionIdentity1893a.log', 'SourceToricResidueMultiplicationIdentity-1899.exit', 'SourceToricResidueMultiplicationIdentity-1899.log', 'SourceToricResidueMultiplicationIdentity.lean', 'SourceToricResidueMultiplicationIdentity1895a.exit', 'SourceToricResidueMultiplicationIdentity1895a.lean', 'SourceToricResidueMultiplicationIdentity1895a.log', 'anthropic-gamma-one-point-chart-1846/S_ModularCurve_exists_algHom_qExpFunctionFieldC_gammaH_bot_comp_eq_iff_and_comp_diamondPullbackModL_of_transcendental_j.lean.txt', 'anthropic-gamma-one-point-chart-1846/manifest.json', 'anthropic-gamma-one-toric-inputs-1848/S_ModularCurve_exists_point_tateLaurent_nsmul_eq_toricPoint_of_isPrimitiveRoot.lean.txt', 'anthropic-gamma-one-toric-inputs-1848/S_ModularCurve_exists_qExpFunctionFieldC_gammaH_bot_coe_eq_toricPoint_pow_and_diamondPullbackModL_apply_eq.lean.txt', 'anthropic-gamma-one-toric-inputs-1848/manifest.json', 'anthropic-tate-formal-1860b/Def_ModularCurve_TateFormal.lean.txt', 'anthropic-tate-formal-1860b/manifest.json', 'anthropic-toric-addition-1870/S_ModularCurve_toricPoint_add_toricPoint_of_charZero.lean.txt', 'anthropic-toric-addition-1870/manifest.json', 'anthropic-toric-definitions-1851b/Def_ModularCurve_TateSlots.lean.txt', 'anthropic-toric-definitions-1851b/S_ModularCurve_exists_gamma1_isIntegralQExp_fourier_and_toricPoint_eq_sum.lean.txt', 'anthropic-toric-definitions-1851b/manifest.json', 'audit_integral_toric_forms_1869.ps1', 'audit_integral_toric_forms_1872.ps1', 'audit_original_toric_coordinates_1883.ps1', 'audit_original_toric_coordinates_1883b.ps1', 'audit_original_toric_coordinates_1883c.ps1', 'audit_toric_marked_point_1899.ps1', 'build_integral_toric_forms_canonical_1869.ps1', 'build_integral_toric_forms_canonical_1872.ps1', 'build_original_toric_coordinates_canonical_1883.ps1', 'integral-toric-forms-audit-failure-1869.json', 'integral-toric-forms-preparation-failure-1869.json', 'integral-toric-forms-superseded-source-archive-1872.json', 'integral-toric-forms-versions-1869.json', 'integral-toric-forms-versions-1872.json', 'original-toric-coordinates-audit-failure-1883.json', 'original-toric-coordinates-dependency-failure-1883.json', 'original-toric-coordinates-versions-1883.json', 'prepare_integral_toric_forms_audit_1869.py', 'prepare_integral_toric_forms_audit_1869b.py', 'prepare_integral_toric_forms_audit_1872.py', 'prepare_original_toric_coordinates_audit_1883.py', 'record_integral_toric_forms_1869.py', 'record_integral_toric_forms_1872.py', 'record_original_toric_coordinates_1883.py', 'record_original_toric_coordinates_1883b.py', 'record_original_toric_coordinates_1883c.py', 'record_toric_marked_point_1899.py', 'source-integral-toric-forms-1-audit-config.json', 'source-integral-toric-forms-2-audit-config.json', 'source-integral-toric-forms-2-reuse-review-20261029.json', 'source-integral-toric-forms-2-scratch-receipt.json', 'source-integral-toric-forms-audit-route-1869.json', 'source-integral-toric-forms-audit-route-1872.json', 'source-original-toric-coordinates-1-audit-config.json', 'source-original-toric-coordinates-2-audit-config.json', 'source-original-toric-coordinates-3-audit-config.json', 'source-original-toric-coordinates-3-reuse-review-20261029.json', 'source-original-toric-coordinates-3-scratch-receipt.json', 'source-original-toric-coordinates-audit-route-1883.json', 'source-toric-marked-point-1-audit-config.json', 'source-toric-marked-point-1-reuse-review-20261029.json', 'source-toric-marked-point-1-scratch-receipt.json', 'source-toric-marked-point-audit-route-1899.json', 'toric-analytic-specialization-route-1891.json', 'toric-marked-point-promotion-route-1901.json', 'toric-marked-point-versions-1899.json']]
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
supplemental_review_path=r/archive_rel/'toric-marked-point-promotion-route-1901.json'

audit = r / "Extension/Dubon2026/Audit.lean"
at = audit.read_text(encoding="utf-8")
for n in queries:
    assert not re.search(r"``" + re.escape(n) + r"(?=[,\s])", at)
tm, dm = "\n]\n\nprivate def publicConstructions", "\n]\n\nprivate def runAudit"
assert at.count(tm) == at.count(dm) == 1
at = at.replace(tm, "".join("\n  ,``" + n for n in theorems) + tm, 1)
at = at.replace(dm, "".join("\n  ," + chr(96)*2 + n for n in defs) + dm, 1)
research_path = r / "Tools/lean-reuse-audit-20261020.json"
reuse_path = r / "Tools/source-toric-marked-point.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt9410"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> automorphy -> original all-weight characteristic-zero association -> actual homogeneous Gamma1 Hecke-character realization -> original genus preservation -> reverse genus inequality -> finite elliptic residue fiber bounds -> original-field/full-torsion chart and stabilizer comparison -> exact-order marked point and original-field coordinates.'
discharged = 'Actual weight-two and weight-four Gamma1 modular forms with explicit integral Fourier coefficients reconstruct both required toric invariant functions in the original Gamma1 field. Their actual residue diamond action is proved. The literal integral Tate curve is elliptic in every coefficient characteristic, with c4=E4 and c6=-E6. Native complex period uniformization proves the division and multiplication identities; an injective coefficient localization and the existing prescribed-root reduction transfer them to every positive characteristic away from N, including 2 and 3. For N at least 2 an actual point of exact order N is constructed in an algebraically closed extension of the Laurent field. All its unit-multiple abscissae are identified, and the two functions in the original Gamma1 field equal the actual marked-point invariants under the natural Laurent embedding. No integrality, ratio membership, diamond-action, point-existence, exact-order or coordinate certificate is assumed in these final consumers.'
boundary = 'The original-field/full-torsion chart identification and stabilizer comparison, finite elliptic fiber bounds including characteristics two and three, and reverse genus remain open. The previously proved residue cusp upper bound is retained. Original genus preservation, integral parabolic transfer, exceptional-prime removal, two-dimensional characteristic-zero realization, original all-weight association, remaining local/image/regularity inputs, automorphy and literal higher continuation remain required. Acceptance stays 16/20; DUB-17--20 OPEN; every original source and verification criterion is unchanged.'
status = 'The 40-module scratch scope passes 220 public axiom queries, 332 exhaustive theorem checks, sixteen linters per module and three declaration-value audits with 186 required dependencies, with zero diagnostics. Production aggregate, focused audits and sequential foundation/paper verification of the 9,450-module scope are pending.'
route = 'The October 29 reuse refresh is applied to this exact source dependency. The native GammaOne.divisionForm supplies the weight-two form, and native finite Fourier orthogonality and coefficient formulas supply the integral reconstruction. Native periodModelHom, its lattice kernel, q expansion maps, prescribed primitive-root reduction, ordinate existence and division-polynomial numerator coprimality replace a new general nonarchimedean uniformization theory. Only localization at the level is needed. The chart already works over an algebraically closed generic torsion field, so no separate Laurent-valued ordinate construction is needed. The pinned external proof is an inert mathematical reference; no external module is imported or built. Three scopes are promoted by import qualification only; all mathematical statements, bodies and comments stay frozen. All public/private/generated axiom checks, sixteen linters per module, 186 required VALUE dependencies, exact ownership and sequential foundation/paper verification remain mandatory. Frozen paper, root pins and owner-only BAT are unchanged. Historical scope reports retain their original boundaries; this combined status supersedes them.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Original-field coordinates and exact-order marked point (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 9,410-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
corrections = []
count = sum(z['exhaustiveTheorems'] for z in certs)
assert count == 332

docpaths = list(dict.fromkeys(r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]))
for f in docpaths:
    assert "\n\n" in f.read_text(encoding="utf-8")
readmes = [(r.parent / "README.md", "Current Project 83 status ("), (repo / "README.md", "Project 83 has an ")]
for f, prefix in readmes:
    assert sum(line.startswith(prefix) for line in f.read_text(encoding="utf-8").splitlines()) == 1
arch = r / "Dubon Architecture.md"
edge = '  CUSPBOUND9410["Full-field diamond covariance, exact j/j_N cusp charts, all-fiber cusp stabilizers and actual residue-image cusp upper count proved. Finite elliptic fiber bounds, reverse genus and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourceToricMarkedPointProductionAudit9450.lean',p/'source-toric-marked-point-9450-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production9450.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/original-residue-cusp-bounds-20261029-1854'
registered = {row['path'] for row in c['files']}
for priorFile in priorArchive.iterdir():
    rel = priorFile.relative_to(r).as_posix()
    if priorFile.is_file() and rel not in registered:
        c['files'].append({'path': rel, 'role': 'Tools'})

reportSource = p / 'Dubon Toric Marked Point Assessment 2026-10-29.md'
assert sha(reportSource) == '4CB1F2893922CBD61D43DA223592BDC539DECE43FCCA11B86ED9E74B252BAAE4'
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
    "productionModules": 9450, "modules": newmods, "queries": queries,
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
arch.write_text(arch.read_text(encoding='utf-8').replace(edge,'  CUSPBOUND9410["Actual diamond-equivariant j/j_N cusp charts and residue-image cusp upper count proved (DUB-17/18)"] --> TORICPOINT9450\n  TORICPOINT9450["Integral original-field coordinates, actual diamond action and exact-order marked point with matching invariants proved. Full torsion chart, stabilizers, finite elliptic fibers, reverse genus and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'),encoding='utf-8')



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Original-field coordinates and exact-order marked point - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-toric-marked-point.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub('  logInfo m!".*"\n', '  logInfo m!"SOURCE TORIC MARKED POINT AUDIT PASS: {count} theorems including private/generated declarations. Original-field toric coordinates and exact-order marked point proved. Finite elliptic bounds, reverse genus and source gates OPEN;16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourceToricMarkedPointProductionAudit9450.lean").write_text(out, encoding="utf-8")
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
    target = p / (source.stem + "Production9450.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
(p / "source-toric-marked-point-9450-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 9450, "increment": 40, "queries": 220,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
