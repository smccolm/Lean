from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 8968
assert d["appliedSourceParabolicDiamondComparison"]["receipt8968"]["exit"] == 0
assert (p / "paper-verification-8968-console.exit").read_text().strip() == "0"
assert (r/'Tools/parabolic-diamond-comparison-20261028-1196/canonical-evidence-8968.json').exists()
key = "appliedSourceArithmeticDiamondComparison"
assert key not in d
digests = {'source-gamma-one-diamond-field-1-scratch-receipt.json': '2C88FCF5A877C1013EF26B7AD692794F62E8B802C24E6F1F5C30AD10F925E48E', 'source-gamma-one-arithmetic-diamond-1-scratch-receipt.json': 'B89848E9494C575A104ED4738CA5A5F60392256296AB6B7C80BAF52D708FE2BA', 'source-diamond-picard-periods-1-scratch-receipt.json': '0F2ECC812E980A04BCCE66B769B8EDD3281C8BC4FEF8C44625B25F910F23EEF2', 'source-diamond-galois-1-scratch-receipt.json': '0A368CDFA4AE5591D280BAAC9EFCFFDEE4420680B385056DD1F43F4BCCA6253E', 'source-diamond-normalizer-1-scratch-receipt.json': '83AC8D1D5E4E2A5320907B0B210A9A7EA833C507F763BDB0944A2F1FE912811E'}

for name, digest in digests.items():
    assert sha(p / name) == digest
certs = [json.loads((p / name).read_text(encoding="utf-8")) for name in digests]
mods = [m for z in certs for m in z["modules"]]
queries = [q for z in certs for q in z["queries"]]
theorems = [q for z in certs for q in z["theoremRegistrations"]]
defs = [q for z in certs for q in z["constructionRegistrations"]]
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (39, 39, 111, 92, 19)
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
archive_rel='Tools/arithmetic-diamond-comparison-20261028-1241'
evidence=[p/'arithmetic-diamond-comparison-promotion-route-1241.json']
evidence += [p/n for n in ['SourceCurveFieldEquivPicard.lean', 'SourceCurveFieldEquivPicard1210a.exit', 'SourceCurveFieldEquivPicard1210a.log', 'SourceCurveFieldEquivPicard1210b.exit', 'SourceCurveFieldEquivPicard1210b.log', 'SourceCyclotomicDiamondCovariance.lean', 'SourceCyclotomicDiamondCovariance1223a.exit', 'SourceCyclotomicDiamondCovariance1223a.log', 'SourceCyclotomicDiamondCovariance1223b.exit', 'SourceCyclotomicDiamondCovariance1223b.log', 'SourceDiamondGaloisAudit1.exit', 'SourceDiamondGaloisAudit1.lean', 'SourceDiamondGaloisAudit1.log', 'SourceDiamondGaloisDependencyAudit1.exit', 'SourceDiamondGaloisDependencyAudit1.lean', 'SourceDiamondGaloisDependencyAudit1.log', 'SourceDiamondGaloisScratchOwnership1234.exit', 'SourceDiamondGaloisScratchOwnership1234.lean', 'SourceDiamondGaloisScratchOwnership1234.log', 'SourceDiamondNormalizerAudit1.exit', 'SourceDiamondNormalizerAudit1.lean', 'SourceDiamondNormalizerAudit1.log', 'SourceDiamondNormalizerDependencyAudit1.exit', 'SourceDiamondNormalizerDependencyAudit1.lean', 'SourceDiamondNormalizerDependencyAudit1.log', 'SourceDiamondNormalizerScratchOwnership1241.exit', 'SourceDiamondNormalizerScratchOwnership1241.lean', 'SourceDiamondNormalizerScratchOwnership1241.log', 'SourceDiamondPicardPeriodsAudit1.exit', 'SourceDiamondPicardPeriodsAudit1.lean', 'SourceDiamondPicardPeriodsAudit1.log', 'SourceDiamondPicardPeriodsDependencyAudit1.exit', 'SourceDiamondPicardPeriodsDependencyAudit1.lean', 'SourceDiamondPicardPeriodsDependencyAudit1.log', 'SourceDiamondPicardPeriodsScratchOwnership1220.exit', 'SourceDiamondPicardPeriodsScratchOwnership1220.lean', 'SourceDiamondPicardPeriodsScratchOwnership1220.log', 'SourceGammaOneArithmeticDiamond.lean', 'SourceGammaOneArithmeticDiamond1209a.exit', 'SourceGammaOneArithmeticDiamond1209a.log', 'SourceGammaOneArithmeticDiamond1209b.exit', 'SourceGammaOneArithmeticDiamond1209b.log', 'SourceGammaOneArithmeticDiamondAudit1.exit', 'SourceGammaOneArithmeticDiamondAudit1.lean', 'SourceGammaOneArithmeticDiamondAudit1.log', 'SourceGammaOneArithmeticDiamondDependencyAudit1.exit', 'SourceGammaOneArithmeticDiamondDependencyAudit1.lean', 'SourceGammaOneArithmeticDiamondDependencyAudit1.log', 'SourceGammaOneArithmeticDiamondGalois.lean', 'SourceGammaOneArithmeticDiamondGalois1232a.exit', 'SourceGammaOneArithmeticDiamondGalois1232a.log', 'SourceGammaOneArithmeticDiamondGenerators.lean', 'SourceGammaOneArithmeticDiamondGenerators1231a.exit', 'SourceGammaOneArithmeticDiamondGenerators1231a.log', 'SourceGammaOneArithmeticDiamondScratchOwnership1212.exit', 'SourceGammaOneArithmeticDiamondScratchOwnership1212.lean', 'SourceGammaOneArithmeticDiamondScratchOwnership1212.log', 'SourceGammaOneArithmeticDiamondTate.lean', 'SourceGammaOneArithmeticDiamondTate1219a.exit', 'SourceGammaOneArithmeticDiamondTate1219a.log', 'SourceGammaOneBinaryDiamondLabels.lean', 'SourceGammaOneBinaryDiamondLabels1240a.exit', 'SourceGammaOneBinaryDiamondLabels1240a.log', 'SourceGammaOneBinaryDiamondTateH1.lean', 'SourceGammaOneBinaryDiamondTateH11222a.exit', 'SourceGammaOneBinaryDiamondTateH11222a.log', 'SourceGammaOneBinaryNormalizerTate.lean', 'SourceGammaOneBinaryNormalizerTate1239a.exit', 'SourceGammaOneBinaryNormalizerTate1239a.log', 'SourceGammaOneBinaryNormalizerTate1239b.exit', 'SourceGammaOneBinaryNormalizerTate1239b.log', 'SourceGammaOneDiamondAnalyticDivisors.lean', 'SourceGammaOneDiamondAnalyticDivisors1215a.exit', 'SourceGammaOneDiamondAnalyticDivisors1215a.log', 'SourceGammaOneDiamondAnalyticGerms.lean', 'SourceGammaOneDiamondAnalyticGerms1213a.exit', 'SourceGammaOneDiamondAnalyticGerms1213a.log', 'SourceGammaOneDiamondAnalyticPlaces.lean', 'SourceGammaOneDiamondAnalyticPlaces1214a.exit', 'SourceGammaOneDiamondAnalyticPlaces1214a.log', 'SourceGammaOneDiamondAnalyticPlaces1214b.exit', 'SourceGammaOneDiamondAnalyticPlaces1214b.log', 'SourceGammaOneDiamondArithmeticLift.lean', 'SourceGammaOneDiamondArithmeticLift1208a.exit', 'SourceGammaOneDiamondArithmeticLift1208a.log', 'SourceGammaOneDiamondArithmeticLift1208b.exit', 'SourceGammaOneDiamondArithmeticLift1208b.log', 'SourceGammaOneDiamondArithmeticLift1208c.exit', 'SourceGammaOneDiamondArithmeticLift1208c.log', 'SourceGammaOneDiamondArithmeticRelation.lean', 'SourceGammaOneDiamondArithmeticRelation1205a.exit', 'SourceGammaOneDiamondArithmeticRelation1205a.log', 'SourceGammaOneDiamondArithmeticRelation1205b.exit', 'SourceGammaOneDiamondArithmeticRelation1205b.log', 'SourceGammaOneDiamondCoefficient.lean', 'SourceGammaOneDiamondCoefficient1235a.exit', 'SourceGammaOneDiamondCoefficient1235a.log', 'SourceGammaOneDiamondCoefficient1235b.exit', 'SourceGammaOneDiamondCoefficient1235b.log', 'SourceGammaOneDiamondCoefficientMatrix.lean', 'SourceGammaOneDiamondCoefficientMatrix1237a.exit', 'SourceGammaOneDiamondCoefficientMatrix1237a.log', 'SourceGammaOneDiamondCoefficientMatrix1237b.exit', 'SourceGammaOneDiamondCoefficientMatrix1237b.log', 'SourceGammaOneDiamondCoefficientMatrix1237c.exit', 'SourceGammaOneDiamondCoefficientMatrix1237c.log', 'SourceGammaOneDiamondComplexArithmetic.lean', 'SourceGammaOneDiamondComplexArithmetic1230a.exit', 'SourceGammaOneDiamondComplexArithmetic1230a.log', 'SourceGammaOneDiamondComplexArithmetic1230b.exit', 'SourceGammaOneDiamondComplexArithmetic1230b.log', 'SourceGammaOneDiamondComplexComparison.lean', 'SourceGammaOneDiamondComplexComparison1218a.exit', 'SourceGammaOneDiamondComplexComparison1218a.log', 'SourceGammaOneDiamondEndpoint.lean', 'SourceGammaOneDiamondEndpoint1216a.exit', 'SourceGammaOneDiamondEndpoint1216a.log', 'SourceGammaOneDiamondFieldAudit1.exit', 'SourceGammaOneDiamondFieldAudit1.lean', 'SourceGammaOneDiamondFieldAudit1.log', 'SourceGammaOneDiamondFieldDependencyAudit1.exit', 'SourceGammaOneDiamondFieldDependencyAudit1.lean', 'SourceGammaOneDiamondFieldDependencyAudit1.log', 'SourceGammaOneDiamondFieldHom.lean', 'SourceGammaOneDiamondFieldHom1199a.exit', 'SourceGammaOneDiamondFieldHom1199a.log', 'SourceGammaOneDiamondFieldHom1199b.exit', 'SourceGammaOneDiamondFieldHom1199b.log', 'SourceGammaOneDiamondFieldJ.lean', 'SourceGammaOneDiamondFieldJ1201a.exit', 'SourceGammaOneDiamondFieldJ1201a.log', 'SourceGammaOneDiamondFieldLabels.lean', 'SourceGammaOneDiamondFieldLabels1200a.exit', 'SourceGammaOneDiamondFieldLabels1200a.log', 'SourceGammaOneDiamondFieldRatios.lean', 'SourceGammaOneDiamondFieldRatios1197a.exit', 'SourceGammaOneDiamondFieldRatios1197a.log', 'SourceGammaOneDiamondFieldRatios1197b.exit', 'SourceGammaOneDiamondFieldRatios1197b.log', 'SourceGammaOneDiamondFieldRatios1197c.exit', 'SourceGammaOneDiamondFieldRatios1197c.log', 'SourceGammaOneDiamondFieldScratchOwnership1204.exit', 'SourceGammaOneDiamondFieldScratchOwnership1204.lean', 'SourceGammaOneDiamondFieldScratchOwnership1204.log', 'SourceGammaOneDiamondGaloisPicard.lean', 'SourceGammaOneDiamondGaloisPicard1233a.exit', 'SourceGammaOneDiamondGaloisPicard1233a.log', 'SourceGammaOneDiamondLabels.lean', 'SourceGammaOneDiamondPeriodInclusion.lean', 'SourceGammaOneDiamondPeriodInclusion1221a.exit', 'SourceGammaOneDiamondPeriodInclusion1221a.log', 'SourceGammaOneDiamondPicard.lean', 'SourceGammaOneDiamondPicard1211a.exit', 'SourceGammaOneDiamondPicard1211a.log', 'SourceGammaOneDiamondPicardPeriods.lean', 'SourceGammaOneDiamondPicardPeriods1217a.exit', 'SourceGammaOneDiamondPicardPeriods1217a.log', 'SourceGammaOneDiamondRationalGenerators.lean', 'SourceGammaOneDiamondRationalGenerators1229a.exit', 'SourceGammaOneDiamondRationalGenerators1229a.log', 'SourceGammaOneDiamondRationalGenerators1229b.exit', 'SourceGammaOneDiamondRationalGenerators1229b.log', 'SourceGammaOneDiamondRestriction.lean', 'SourceGammaOneDiamondRestriction1236a.exit', 'SourceGammaOneDiamondRestriction1236a.log', 'SourceGammaOneDiamondRestriction1236b.exit', 'SourceGammaOneDiamondRestriction1236b.log', 'SourceGammaOneFieldCuspGerm.lean', 'SourceGammaOneFieldCuspGerm1198a.exit', 'SourceGammaOneFieldCuspGerm1198a.log', 'SourceLaurentAlgebraicCoefficient.lean', 'SourceLaurentAlgebraicCoefficient1202a.exit', 'SourceLaurentAlgebraicCoefficient1202a.log', 'SourceLaurentAlgebraicCoefficient1202b.exit', 'SourceLaurentAlgebraicCoefficient1202b.log', 'SourceLaurentAlgebraicCoefficient1202c.exit', 'SourceLaurentAlgebraicCoefficient1202c.log', 'SourceLaurentAlgebraicallyClosedLift.lean', 'SourceLaurentAlgebraicallyClosedLift1203a.exit', 'SourceLaurentAlgebraicallyClosedLift1203a.log', 'SourceLaurentCoefficientProjection.lean', 'SourceLaurentCoefficientProjection1206a.exit', 'SourceLaurentCoefficientProjection1206a.log', 'SourceLaurentCoefficientProjection1206b.exit', 'SourceLaurentCoefficientProjection1206b.log', 'SourceLaurentCoefficientProjection1206c.exit', 'SourceLaurentCoefficientProjection1206c.log', 'SourceLaurentFieldIntersection.lean', 'SourceLaurentFieldIntersection1207b.exit', 'SourceLaurentFieldIntersection1207b.log', 'SourceLaurentFieldIntersection1207c.exit', 'SourceLaurentFieldIntersection1207c.log', 'SourceLaurentFieldIntersection1207d.exit', 'SourceLaurentFieldIntersection1207d.log', 'SourceRationalCuspDiamondImage.lean', 'SourceRationalCuspDiamondImage1225a.exit', 'SourceRationalCuspDiamondImage1225a.log', 'SourceRationalDiamondCoefficients.lean', 'SourceRationalDiamondCoefficients1228a.exit', 'SourceRationalDiamondCoefficients1228a.log', 'SourceRationalDiamondCoefficients1228b.exit', 'SourceRationalDiamondCoefficients1228b.log', 'SourceRationalDiamondFraction.lean', 'SourceRationalDiamondFraction1224a.exit', 'SourceRationalDiamondFraction1224a.log', 'SourceRationalDiamondQuotientGerm.lean', 'SourceRationalDiamondQuotientGerm1227a.exit', 'SourceRationalDiamondQuotientGerm1227a.log', 'SourceRationalModularCuspQuotient.lean', 'SourceRationalModularCuspQuotient1226a.exit', 'SourceRationalModularCuspQuotient1226a.log', 'SourceRationalModularCuspQuotient1226b.exit', 'SourceRationalModularCuspQuotient1226b.log', 'arithmetic-diamond-comparison-promotion-route-1241.json', 'audit_diamond_galois_1234.ps1', 'audit_diamond_normalizer_1241.ps1', 'audit_diamond_picard_periods_1220.ps1', 'audit_gamma_one_arithmetic_diamond_1212.ps1', 'audit_gamma_one_diamond_field_1204.ps1', 'compile_arithmetic_diamond_1209a.ps1', 'compile_arithmetic_diamond_1209b.ps1', 'compile_arithmetic_diamond_galois_1232a.ps1', 'compile_arithmetic_diamond_generators_1231a.ps1', 'compile_arithmetic_diamond_tate_1219a.ps1', 'compile_binary_diamond_labels_1240a.ps1', 'compile_binary_diamond_tate_h1_1222a.ps1', 'compile_binary_normalizer_tate_1239a.ps1', 'compile_binary_normalizer_tate_1239b.ps1', 'compile_cyclotomic_diamond_covariance_1223a.ps1', 'compile_cyclotomic_diamond_covariance_1223b.ps1', 'compile_diamond_analytic_divisors_1215a.ps1', 'compile_diamond_analytic_germs_1213a.ps1', 'compile_diamond_analytic_places_1214a.ps1', 'compile_diamond_analytic_places_1214b.ps1', 'compile_diamond_arithmetic_lift_1208a.ps1', 'compile_diamond_arithmetic_lift_1208b.ps1', 'compile_diamond_arithmetic_lift_1208c.ps1', 'compile_diamond_arithmetic_relation_1205a.ps1', 'compile_diamond_arithmetic_relation_1205b.ps1', 'compile_diamond_coefficient_1235a.ps1', 'compile_diamond_coefficient_matrix_1237a.ps1', 'compile_diamond_coefficient_matrix_1237b.ps1', 'compile_diamond_complex_arithmetic_1230a.ps1', 'compile_diamond_complex_arithmetic_1230b.ps1', 'compile_diamond_complex_comparison_1218a.ps1', 'compile_diamond_endpoint_1216a.ps1', 'compile_diamond_field_hom_1199a.ps1', 'compile_diamond_field_hom_1199b.ps1', 'compile_diamond_field_j_1201a.ps1', 'compile_diamond_field_labels_1200a.ps1', 'compile_diamond_field_ratios_1197a.ps1', 'compile_diamond_field_ratios_1197b.ps1', 'compile_diamond_field_ratios_1197c.ps1', 'compile_diamond_galois_picard_1233a.ps1', 'compile_diamond_period_inclusion_1221a.ps1', 'compile_diamond_picard_1211a.ps1', 'compile_diamond_picard_periods_1217a.ps1', 'compile_diamond_rational_generators_1229a.ps1', 'compile_diamond_rational_generators_1229b.ps1', 'compile_diamond_restriction_1236a.ps1', 'compile_field_cusp_germ_1198a.ps1', 'compile_field_equiv_picard_1210a.ps1', 'compile_field_equiv_picard_1210b.ps1', 'compile_laurent_algebraic_coefficient_1202a.ps1', 'compile_laurent_algebraic_coefficient_1202b.ps1', 'compile_laurent_algebraic_coefficient_1202c.ps1', 'compile_laurent_closed_lift_1203a.ps1', 'compile_laurent_field_intersection_1207a.ps1', 'compile_laurent_field_intersection_1207b.ps1', 'compile_laurent_field_intersection_1207c.ps1', 'compile_laurent_field_intersection_1207d.ps1', 'compile_laurent_projection_1206a.ps1', 'compile_laurent_projection_1206b.ps1', 'compile_laurent_projection_1206c.ps1', 'compile_rational_cusp_diamond_image_1225a.ps1', 'compile_rational_diamond_coefficients_1228a.ps1', 'compile_rational_diamond_coefficients_1228b.ps1', 'compile_rational_diamond_fraction_1224a.ps1', 'compile_rational_diamond_quotient_germ_1227a.ps1', 'compile_rational_modular_cusp_quotient_1226a.ps1', 'compile_rational_modular_cusp_quotient_1226b.ps1', 'consumers1201-focus.log', 'consumers1201.txt', 'consumers1212-focus.log', 'consumers1212.txt', 'consumers1221-focus.log', 'consumers1221.txt', 'consumers1234-focus.log', 'consumers1234.txt', 'diamond-arithmetic-descent-route-1202.md', 'diamond-field-route-1197.md', 'diamond-picard-period-route-1213.md', 'docs1201.py', 'docs1212.py', 'docs1221.py', 'docs1234.py', 'foundation1201-console.log', 'foundation1212-console.log', 'foundation1221-console.log', 'foundation1234-console.log', 'modules1201.json', 'modules1212.json', 'modules1221.json', 'modules1234.json', 'paper1201-console.log', 'paper1212-console.log', 'paper1221-console.log', 'paper1234-console.log', 'prepare_arithmetic_diamond_galois_1232.py', 'prepare_diamond_galois_audit_1234.py', 'prepare_diamond_normalizer_audit_1241.py', 'prepare_diamond_picard_periods_audit_1220.py', 'prepare_gamma_one_arithmetic_diamond_audit_1212.py', 'prepare_gamma_one_diamond_field_audit_1204.py', 'recompile_normalizer_imports_1238.ps1', 'record1201.py', 'record1212.py', 'record1221.py', 'record1234.py', 'record_diamond_galois_1234.py', 'record_diamond_normalizer_1241.py', 'record_diamond_picard_periods_1220.py', 'record_gamma_one_arithmetic_diamond_1212.py', 'record_gamma_one_diamond_field_1204.py', 'register1201.py', 'register1212.py', 'register1221.py', 'register1234.py', 'registrations1201.json', 'registrations1212.json', 'registrations1221.json', 'registrations1234.json', 'section1201.txt', 'section1212.txt', 'section1221.txt', 'section1234.txt', 'source-diamond-galois-1-audit-config.json', 'source-diamond-galois-1-reuse-review-20261028.json', 'source-diamond-galois-1-scratch-receipt.json', 'source-diamond-galois-audit-route-1234.json', 'source-diamond-normalizer-1-audit-config.json', 'source-diamond-normalizer-1-reuse-review-20261028.json', 'source-diamond-normalizer-1-scratch-receipt.json', 'source-diamond-normalizer-audit-route-1241.json', 'source-diamond-picard-periods-1-audit-config.json', 'source-diamond-picard-periods-1-reuse-review-20261028.json', 'source-diamond-picard-periods-1-scratch-receipt.json', 'source-diamond-picard-periods-audit-route-1220.json', 'source-gamma-one-arithmetic-diamond-1-audit-config.json', 'source-gamma-one-arithmetic-diamond-1-reuse-review-20261028.json', 'source-gamma-one-arithmetic-diamond-1-scratch-receipt.json', 'source-gamma-one-arithmetic-diamond-audit-route-1212.json', 'source-gamma-one-diamond-field-1-audit-config.json', 'source-gamma-one-diamond-field-1-reuse-review-20261028.json', 'source-gamma-one-diamond-field-1-scratch-receipt.json', 'source-gamma-one-diamond-field-audit-route-1204.json', 'source-gamma-one-diamond-period-1-scratch-receipt.json', 'source-gamma-one-diamond-tate-1-scratch-receipt.json', 'status1201.txt', 'status1212.txt', 'status1221.txt', 'status1234.txt']]
for folder in ['arithmetic-diamond-1209a', 'binary-normalizer-tate-1239a', 'cyclotomic-diamond-covariance-1223a', 'diamond-analytic-places-1214a', 'diamond-arithmetic-lift-1208a', 'diamond-arithmetic-lift-1208b', 'diamond-arithmetic-relation-1205a', 'diamond-coefficient-matrix-1237a', 'diamond-complex-arithmetic-1230a', 'diamond-field-hom-1199a', 'diamond-field-ratios-1197a', 'diamond-field-ratios-1197b', 'diamond-rational-generators-1229a', 'field-equiv-picard-1210a', 'laurent-algebraic-coefficient-1202a', 'laurent-algebraic-coefficient-1202b', 'laurent-field-intersection-1207b', 'laurent-field-intersection-1207c', 'laurent-projection-1206a', 'laurent-projection-1206b', 'normalizer-imports-1235a', 'normalizer-imports-1236a', 'normalizer-imports-1237b', 'rational-diamond-coefficients-1228a', 'rational-modular-cusp-quotient-1226a']:
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
supplemental_review_path=r/archive_rel/'arithmetic-diamond-comparison-promotion-route-1241.json'

audit = r / "Extension/Dubon2026/Audit.lean"
at = audit.read_text(encoding="utf-8")
for n in queries:
    assert not re.search(r"``" + re.escape(n) + r"(?=[,\s])", at)
tm, dm = "\n]\n\nprivate def publicConstructions", "\n]\n\nprivate def runAudit"
assert at.count(tm) == at.count(dm) == 1
at = at.replace(tm, "".join("\n  ,``" + n for n in theorems) + tm, 1)
at = at.replace(dm, "".join("\n  ," + chr(96)*2 + n for n in defs) + dm, 1)
research_path = r / "Tools/lean-reuse-audit-20261020.json"
reuse_path = r / "Tools/source-arithmetic-diamond-comparison.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt8968"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> arithmetic realization of original finite Gamma1 homogeneous-coefficient Hecke characters -> original arithmetic diamond, Picard/period/Tate comparison, Galois commutation and exact homogeneous normalizer coefficient convention.'
discharged = 'The literal Gamma0 diamond is constructed on the original complex modular-ratio field and descended to the original algebraic-closure field. Its original j-coordinate, constants, quotient and cusp-germ identities are proved. The actual field action induces the original place, divisor and Picard action. Existing analytic representatives and the moving lemma prove the complete complex Picard-period square, including the degree-zero cancellation of the basepoint term; unique constant-field place extension proves the arithmetic conorm square. The same arithmetic diamond therefore acts on the original Picard Tate module and integral period tensor as the actual dual slash diamond. Cyclotomic Fricke covariance, rational fixed-field descent and genuine rational cusp quotients prove rationality of diamond images of the original integral modular-ratio generators, discharging all auxiliary fraction and germ inputs. Original field generation then proves Galois commutation on both fields and on the original arithmetic places, divisors, Picard group and Tate module. The actual diagonal-cover normalizer determines the inverse original binary coefficient action; it fixes literal restrictions of original cocycles and H1 classes, equals homogeneous substitution by the reversed diagonal entries modulo the coefficient modulus, and depends only on the lower-right unit label. The original arithmetic Tate dual/H1 diamond comparison consumes precisely that coefficient formula and commutes with Galois. No replacement modular-curve or coefficient model is introduced.'
boundary = 'The original arithmetic diamond, full Picard/period/Tate compatibility, Galois commutation and homogeneous normalizer coefficient convention are now proved. The exact geometric lifting condition sourceGammaOneIntegralParabolicTransfer remains unproved, so the existing finite parabolic character descent remains conditional and excludes primes dividing its fixed nonzero integer. Exceptional primes, coefficient-field/Frobenius/inertia realization, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain. Finite characters do not supply a characteristic-zero lift. 16/20; DUB-17--20 OPEN; all twenty acceptance gates unchanged.'
status = 'The thirty-nine-module original arithmetic diamond and homogeneous comparison scope passes 111 public axiom queries, 196 exhaustive scratch theorem checks, sixteen linters per module and five declaration-value audits with 172 required dependency checks, with zero diagnostics. Production aggregate, focused audits and sequential foundation/paper verification of the 9,007-module scope are pending.'
route = 'The October 28 upstream refresh supplied the single-coset diamond route, adapted to the existing native objects. Before extending dependencies, reuse checks selected original modular quotients and injective cusp germs for the complex field, a native linear coefficient projection and finite-span quotient argument for scalar intersection, and the original finite j-relation for arithmetic descent. Existing analytic Picard surjectivity avoids a new cusp-by-cusp presentation. Existing cyclotomic Fricke covariance and rational cusp normalization avoid a new rational modular-curve model or automorphism extension to C. Native cocycle identities and the already proved diagonal-cover triviality identify the actual coefficient convention. The exact original arithmetic Tate/H1 consumer then composes those results. Historical scratch receipts retain their then-open obligations; the current assembled assessment supersedes those boundaries. Frozen mathematical bodies are promoted by import qualification only.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Original arithmetic diamond, Galois and homogeneous coefficient comparison (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 8,968-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
corrections = []
count = sum(z['exhaustiveTheorems'] for z in certs)
assert count == 196

docpaths = list(dict.fromkeys(r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]))
for f in docpaths:
    assert "\n\n" in f.read_text(encoding="utf-8")
readmes = [(r.parent / "README.md", "Current Project 83 status ("), (repo / "README.md", "Project 83 has an ")]
for f, prefix in readmes:
    assert sum(line.startswith(prefix) for line in f.read_text(encoding="utf-8").splitlines()) == 1
arch = r / "Dubon Architecture.md"
edge = '  PARABDIAM8968["Original parabolic operator congruences at all precisions away from one fixed integer proved; actual finite parabolic/Tate word kernels identified. Character descent CONDITIONAL on exact parabolic transfer preimages. Native/period diamonds and original finite H1 transpose proved. Exceptions, arithmetic Picard diamond, coefficient action, Galois realization and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourceArithmeticDiamondComparisonProductionAudit9007.lean',p/'source-arithmetic-diamond-comparison-9007-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production9007.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/parabolic-diamond-comparison-20261028-1196'
registered = {row['path'] for row in c['files']}
for priorFile in priorArchive.iterdir():
    rel = priorFile.relative_to(r).as_posix()
    if priorFile.is_file() and rel not in registered:
        c['files'].append({'path': rel, 'role': 'Tools'})

reportSource = p / 'Dubon Arithmetic Diamond Reuse Assessment 2026-10-28.md'
assert sha(reportSource) == '7B6BE65CE9082F4C1586F6B6D6E72B4A9442D593241D8808432FF1CCF94CCA7A'
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
    "productionModules": 9007, "modules": newmods, "queries": queries,
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
arch.write_text(arch.read_text(encoding='utf-8').replace(edge,'  PARABDIAM8968["Original parabolic congruences away from a fixed integer, finite parabolic/Tate word kernel, conditional transfer descent and native/period diamonds proved (DUB-17/18)"] --> ARITHDIAM9007\n  ARITHDIAM9007["Original arithmetic field/Picard/period/Tate diamonds, Galois commutation, exact homogeneous normalizer coefficient action and native finite H1 comparison proved. Parabolic transfer preimages, exceptional primes, Frobenius/inertia, characteristic-zero association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'),encoding='utf-8')



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Original arithmetic diamond, Galois and homogeneous coefficient comparison - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-arithmetic-diamond-comparison.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub('  logInfo m!".*"\\n', '  logInfo m!"SOURCE ARITHMETIC DIAMOND COMPARISON AUDIT PASS: {count} theorems including private/generated declarations. Original arithmetic field/Picard/period/Tate diamonds, actual Galois commutation, exact homogeneous normalizer coefficients and native finite H1 comparison. Parabolic transfer preimages, exceptional primes, Frobenius/inertia and characteristic-zero association remain;16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourceArithmeticDiamondComparisonProductionAudit9007.lean").write_text(out, encoding="utf-8")
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
    target = p / (source.stem + "Production9007.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
(p / "source-arithmetic-diamond-comparison-9007-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 9007, "increment": 39, "queries": 111,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
