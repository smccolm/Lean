from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 9046
assert d["appliedSourceGammaOneReduction"]["receipt9046"]["exit"] == 0
assert (p / "paper-verification-9046-console.exit").read_text().strip() == "0"
assert (r/'Tools/gamma-one-reduction-20261028-1292/canonical-evidence-9046.json').exists()
key = "appliedSourceGammaOneHeckeNorm"
assert key not in d
digests = {'source-gamma-one-hecke-degree-1-scratch-receipt.json': '06F309311D6E9A558A30749CECD02BFA693551BAD9107CCA376913C78B6B5F86', 'source-gamma-one-norm-1-scratch-receipt.json': 'F4449953AAEF79EBF2DEA59C229438C0D4BEB93277034859ECE66AF44DBB454E', 'source-gamma-one-diamond-norm-2-scratch-receipt.json': '8DB8032D96DFB3EBD0A76B1D67A39E4707FCB9921A102C8293C504FF4EB548E5', 'source-gamma-one-diamond-reduction-1-scratch-receipt.json': '3BCC2E3E62001FA3D4070CDE54230B633E030BA41B7926E046017CADE4F64752'}

for name, digest in digests.items():
    assert sha(p / name) == digest
certs = [json.loads((p / name).read_text(encoding="utf-8")) for name in digests]
mods = [m for z in certs for m in z["modules"]]
queries = [q for z in certs for q in z["queries"]]
theorems = [q for z in certs for q in z["theoremRegistrations"]]
defs = [q for z in certs for q in z["constructionRegistrations"]]
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (28, 28, 85, 71, 14)
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
archive_rel='Tools/gamma-one-hecke-norm-20261028-1324'
evidence=[p/'gamma-one-hecke-norm-promotion-route-1324.json']
evidence += [p/n for n in ['SourceGammaOneAdjacentJAnalyticAction.lean', 'SourceGammaOneAdjacentJAnalyticAction1316a.exit', 'SourceGammaOneAdjacentJAnalyticAction1316a.lean.txt', 'SourceGammaOneAdjacentJAnalyticAction1316a.log', 'SourceGammaOneAdjacentJAnalyticAction1316b.exit', 'SourceGammaOneAdjacentJAnalyticAction1316b.lean.txt', 'SourceGammaOneAdjacentJAnalyticAction1316b.log', 'SourceGammaOneAdjacentJAnalyticAction1316c.exit', 'SourceGammaOneAdjacentJAnalyticAction1316c.lean.txt', 'SourceGammaOneAdjacentJAnalyticAction1316c.log', 'SourceGammaOneAdjacentJAnalyticAction1316d.exit', 'SourceGammaOneAdjacentJAnalyticAction1316d.lean.txt', 'SourceGammaOneAdjacentJAnalyticAction1316d.log', 'SourceGammaOneAdjacentJAnalyticAction1316e.exit', 'SourceGammaOneAdjacentJAnalyticAction1316e.log', 'SourceGammaOneAdjacentJArithmeticDiamond.lean', 'SourceGammaOneAdjacentJArithmeticDiamond1318a.exit', 'SourceGammaOneAdjacentJArithmeticDiamond1318a.lean.txt', 'SourceGammaOneAdjacentJArithmeticDiamond1318a.log', 'SourceGammaOneAdjacentJArithmeticDiamond1318b.exit', 'SourceGammaOneAdjacentJArithmeticDiamond1318b.lean.txt', 'SourceGammaOneAdjacentJArithmeticDiamond1318b.log', 'SourceGammaOneAdjacentJArithmeticDiamond1318c.exit', 'SourceGammaOneAdjacentJArithmeticDiamond1318c.lean.txt', 'SourceGammaOneAdjacentJArithmeticDiamond1318c.log', 'SourceGammaOneAdjacentJArithmeticDiamond1318d.exit', 'SourceGammaOneAdjacentJArithmeticDiamond1318d.lean.txt', 'SourceGammaOneAdjacentJArithmeticDiamond1318d.log', 'SourceGammaOneAdjacentJArithmeticDiamond1318e.exit', 'SourceGammaOneAdjacentJArithmeticDiamond1318e.log', 'SourceGammaOneAdjacentJAutomorphism.lean', 'SourceGammaOneAdjacentJAutomorphism1306a.exit', 'SourceGammaOneAdjacentJAutomorphism1306a.lean.txt', 'SourceGammaOneAdjacentJAutomorphism1306a.log', 'SourceGammaOneAdjacentJAutomorphism1306b.exit', 'SourceGammaOneAdjacentJAutomorphism1306b.log', 'SourceGammaOneAdjacentJCoefficients.lean', 'SourceGammaOneAdjacentJCoefficients1307a.exit', 'SourceGammaOneAdjacentJCoefficients1307a.log', 'SourceGammaOneAdjacentJDiamondAction.lean', 'SourceGammaOneAdjacentJDiamondAction1313a.exit', 'SourceGammaOneAdjacentJDiamondAction1313a.lean.txt', 'SourceGammaOneAdjacentJDiamondAction1313a.log', 'SourceGammaOneAdjacentJDiamondAction1313b.exit', 'SourceGammaOneAdjacentJDiamondAction1313b.log', 'SourceGammaOneAdjacentJDiamondMatrix.lean', 'SourceGammaOneAdjacentJDiamondMatrix1312a.exit', 'SourceGammaOneAdjacentJDiamondMatrix1312a.log', 'SourceGammaOneAdjacentJEmbedding.lean', 'SourceGammaOneAdjacentJEmbedding1304a.exit', 'SourceGammaOneAdjacentJEmbedding1304a.log', 'SourceGammaOneAdjacentJGeneration.lean', 'SourceGammaOneAdjacentJGeneration1302a.exit', 'SourceGammaOneAdjacentJGeneration1302a.log', 'SourceGammaOneAdjacentJNonmembership.lean', 'SourceGammaOneAdjacentJNonmembership1301a.exit', 'SourceGammaOneAdjacentJNonmembership1301a.lean.txt', 'SourceGammaOneAdjacentJNonmembership1301a.log', 'SourceGammaOneAdjacentJNonmembership1301b.exit', 'SourceGammaOneAdjacentJNonmembership1301b.log', 'SourceGammaOneAdjacentJPolynomial.lean', 'SourceGammaOneAdjacentJPolynomial1303a.exit', 'SourceGammaOneAdjacentJPolynomial1303a.lean.txt', 'SourceGammaOneAdjacentJPolynomial1303a.log', 'SourceGammaOneAdjacentJPolynomial1303b.exit', 'SourceGammaOneAdjacentJPolynomial1303b.log', 'SourceGammaOneAdjacentJPreservation.lean', 'SourceGammaOneAdjacentJPreservation1305a.exit', 'SourceGammaOneAdjacentJPreservation1305a.lean.txt', 'SourceGammaOneAdjacentJPreservation1305a.log', 'SourceGammaOneAdjacentJPreservation1305b.exit', 'SourceGammaOneAdjacentJPreservation1305b.lean.txt', 'SourceGammaOneAdjacentJPreservation1305b.log', 'SourceGammaOneAdjacentJPreservation1305c.exit', 'SourceGammaOneAdjacentJPreservation1305c.lean.txt', 'SourceGammaOneAdjacentJPreservation1305c.log', 'SourceGammaOneAdjacentJPreservation1305d.exit', 'SourceGammaOneAdjacentJPreservation1305d.log', 'SourceGammaOneAdjacentJRatio.lean', 'SourceGammaOneAdjacentJRatio1299a.exit', 'SourceGammaOneAdjacentJRatio1299a.lean.txt', 'SourceGammaOneAdjacentJRatio1299a.log', 'SourceGammaOneAdjacentJRatio1299b.exit', 'SourceGammaOneAdjacentJRatio1299b.log', 'SourceGammaOneAdjacentJReverseDiamond.lean', 'SourceGammaOneAdjacentJReverseDiamond1317a.exit', 'SourceGammaOneAdjacentJReverseDiamond1317a.lean.txt', 'SourceGammaOneAdjacentJReverseDiamond1317a.log', 'SourceGammaOneAdjacentJReverseDiamond1317b.exit', 'SourceGammaOneAdjacentJReverseDiamond1317b.lean.txt', 'SourceGammaOneAdjacentJReverseDiamond1317b.log', 'SourceGammaOneAdjacentJReverseDiamond1317c.exit', 'SourceGammaOneAdjacentJReverseDiamond1317c.lean.txt', 'SourceGammaOneAdjacentJReverseDiamond1317c.log', 'SourceGammaOneAdjacentJReverseDiamond1317d.exit', 'SourceGammaOneAdjacentJReverseDiamond1317d.lean.txt', 'SourceGammaOneAdjacentJReverseDiamond1317d.log', 'SourceGammaOneAdjacentJReverseDiamond1317e.exit', 'SourceGammaOneAdjacentJReverseDiamond1317e.log', 'SourceGammaOneCoprimeGeneration.lean', 'SourceGammaOneCoprimeGeneration1298a.exit', 'SourceGammaOneCoprimeGeneration1298a.log', 'SourceGammaOneDiamondNormAudit2.exit', 'SourceGammaOneDiamondNormAudit2.lean', 'SourceGammaOneDiamondNormAudit2.log', 'SourceGammaOneDiamondNormDependencyAudit2.exit', 'SourceGammaOneDiamondNormDependencyAudit2.lean', 'SourceGammaOneDiamondNormDependencyAudit2.log', 'SourceGammaOneDiamondNormScratchOwnership1321.lean', 'SourceGammaOneDiamondNormScratchOwnership1321b.exit', 'SourceGammaOneDiamondNormScratchOwnership1321b.lean', 'SourceGammaOneDiamondNormScratchOwnership1321b.log', 'SourceGammaOneDiamondReductionAudit1.exit', 'SourceGammaOneDiamondReductionAudit1.lean', 'SourceGammaOneDiamondReductionAudit1.log', 'SourceGammaOneDiamondReductionDependencyAudit1.exit', 'SourceGammaOneDiamondReductionDependencyAudit1.lean', 'SourceGammaOneDiamondReductionDependencyAudit1.log', 'SourceGammaOneDiamondReductionScratchOwnership1325.exit', 'SourceGammaOneDiamondReductionScratchOwnership1325.lean', 'SourceGammaOneDiamondReductionScratchOwnership1325.log', 'SourceGammaOneHeckeCoordinateDegree.lean', 'SourceGammaOneHeckeCoordinateDegree1295a.exit', 'SourceGammaOneHeckeCoordinateDegree1295a.log', 'SourceGammaOneHeckeDegreeAudit1.exit', 'SourceGammaOneHeckeDegreeAudit1.lean', 'SourceGammaOneHeckeDegreeAudit1.log', 'SourceGammaOneHeckeDegreeDependencyAudit1.exit', 'SourceGammaOneHeckeDegreeDependencyAudit1.lean', 'SourceGammaOneHeckeDegreeDependencyAudit1.log', 'SourceGammaOneHeckeDegreeScratchOwnership1297.exit', 'SourceGammaOneHeckeDegreeScratchOwnership1297.lean', 'SourceGammaOneHeckeDegreeScratchOwnership1297.log', 'SourceGammaOneHeckeDiamondNorm.lean', 'SourceGammaOneHeckeDiamondNorm1319a.exit', 'SourceGammaOneHeckeDiamondNorm1319a.lean.txt', 'SourceGammaOneHeckeDiamondNorm1319a.log', 'SourceGammaOneHeckeDiamondNorm1319b.exit', 'SourceGammaOneHeckeDiamondNorm1319b.log', 'SourceGammaOneHeckeEmbeddingCensus.lean', 'SourceGammaOneHeckeEmbeddingCensus1309a.exit', 'SourceGammaOneHeckeEmbeddingCensus1309a.log', 'SourceGammaOneHeckeIntegralDiamondReduction.lean', 'SourceGammaOneHeckeIntegralDiamondReduction1323a.exit', 'SourceGammaOneHeckeIntegralDiamondReduction1323a.lean.txt', 'SourceGammaOneHeckeIntegralDiamondReduction1323a.log', 'SourceGammaOneHeckeIntegralDiamondReduction1323b.exit', 'SourceGammaOneHeckeIntegralDiamondReduction1323b.lean.txt', 'SourceGammaOneHeckeIntegralDiamondReduction1323b.log', 'SourceGammaOneHeckeIntegralDiamondReduction1323c.exit', 'SourceGammaOneHeckeIntegralDiamondReduction1323c.log', 'SourceGammaOneHeckeMixedLaurentReduction.lean', 'SourceGammaOneHeckeMixedLaurentReduction1322a.exit', 'SourceGammaOneHeckeMixedLaurentReduction1322a.log', 'SourceGammaOneHeckeNormEmbeddings.lean', 'SourceGammaOneHeckeNormEmbeddings1308a.exit', 'SourceGammaOneHeckeNormEmbeddings1308a.lean.txt', 'SourceGammaOneHeckeNormEmbeddings1308a.log', 'SourceGammaOneHeckeNormEmbeddings1308b.exit', 'SourceGammaOneHeckeNormEmbeddings1308b.log', 'SourceGammaOneHeckeNormProduct.lean', 'SourceGammaOneHeckeNormProduct1310a.exit', 'SourceGammaOneHeckeNormProduct1310a.log', 'SourceGammaOneHeckePrimeDegree.lean', 'SourceGammaOneHeckePrimeDegree1296a.exit', 'SourceGammaOneHeckePrimeDegree1296a.log', 'SourceGammaOneHeckePrimeDegree1296b.exit', 'SourceGammaOneHeckePrimeDegree1296b.log', 'SourceGammaOneHeckePrimeDegree1296c.exit', 'SourceGammaOneHeckePrimeDegree1296c.log', 'SourceGammaOneHeckePrimeDegree1296d.exit', 'SourceGammaOneHeckePrimeDegree1296d.log', 'SourceGammaOneNormAudit1.exit', 'SourceGammaOneNormAudit1.lean', 'SourceGammaOneNormAudit1.log', 'SourceGammaOneNormDependencyAudit1.exit', 'SourceGammaOneNormDependencyAudit1.lean', 'SourceGammaOneNormDependencyAudit1.log', 'SourceGammaOneNormScratchOwnership1311.exit', 'SourceGammaOneNormScratchOwnership1311.lean', 'SourceGammaOneNormScratchOwnership1311.log', 'SourceGammaOnePrimeHeckeIndex.lean', 'SourceGammaOnePrimeHeckeIndex1293a.exit', 'SourceGammaOnePrimeHeckeIndex1293a.log', 'SourceGammaOnePrimeHeckeIndex1293b.exit', 'SourceGammaOnePrimeHeckeIndex1293b.log', 'SourceGammaOneRationalAnalyticGerms.lean', 'SourceGammaOneRationalAnalyticGerms1314a.exit', 'SourceGammaOneRationalAnalyticGerms1314a.lean.txt', 'SourceGammaOneRationalAnalyticGerms1314a.log', 'SourceGammaOneRationalAnalyticGerms1314b.exit', 'SourceGammaOneRationalAnalyticGerms1314b.lean.txt', 'SourceGammaOneRationalAnalyticGerms1314b.log', 'SourceGammaOneRationalAnalyticGerms1314c.exit', 'SourceGammaOneRationalAnalyticGerms1314c.log', 'SourceGammaOneRealizationRestriction.lean', 'SourceGammaOneRealizationRestriction1300a.exit', 'SourceGammaOneRealizationRestriction1300a.log', 'SourceGammaOneSignedHeckeIndex.lean', 'SourceGammaOneSignedHeckeIndex1294a.exit', 'SourceGammaOneSignedHeckeIndex1294a.log', 'SourceGammaOneUpperHalfPlaneGermFaithfulness.lean', 'SourceGammaOneUpperHalfPlaneGermFaithfulness1320a.exit', 'SourceGammaOneUpperHalfPlaneGermFaithfulness1320a.log', 'SourceGammaOneUpperHalfPlaneHeckeGerms.lean', 'SourceGammaOneUpperHalfPlaneHeckeGerms1315a.exit', 'SourceGammaOneUpperHalfPlaneHeckeGerms1315a.log', 'audit_gamma_one_diamond_norm_1321.ps1', 'audit_gamma_one_diamond_norm_1321b.ps1', 'audit_gamma_one_diamond_reduction_1325.ps1', 'audit_gamma_one_hecke_degree_1297.ps1', 'audit_gamma_one_norm_1311.ps1', 'compile_gamma_one_adjacent_j_analytic_action_1316a.ps1', 'compile_gamma_one_adjacent_j_analytic_action_1316b.ps1', 'compile_gamma_one_adjacent_j_analytic_action_1316c.ps1', 'compile_gamma_one_adjacent_j_analytic_action_1316d.ps1', 'compile_gamma_one_adjacent_j_analytic_action_1316e.ps1', 'compile_gamma_one_adjacent_j_arithmetic_diamond_1318a.ps1', 'compile_gamma_one_adjacent_j_arithmetic_diamond_1318b.ps1', 'compile_gamma_one_adjacent_j_arithmetic_diamond_1318c.ps1', 'compile_gamma_one_adjacent_j_arithmetic_diamond_1318d.ps1', 'compile_gamma_one_adjacent_j_arithmetic_diamond_1318e.ps1', 'compile_gamma_one_adjacent_j_automorphism_1306a.ps1', 'compile_gamma_one_adjacent_j_automorphism_1306b.ps1', 'compile_gamma_one_adjacent_j_coefficients_1307a.ps1', 'compile_gamma_one_adjacent_j_diamond_action_1313a.ps1', 'compile_gamma_one_adjacent_j_diamond_action_1313b.ps1', 'compile_gamma_one_adjacent_j_diamond_matrix_1312a.ps1', 'compile_gamma_one_adjacent_j_embedding_1304a.ps1', 'compile_gamma_one_adjacent_j_generation_1302a.ps1', 'compile_gamma_one_adjacent_j_nonmembership_1301a.ps1', 'compile_gamma_one_adjacent_j_nonmembership_1301b.ps1', 'compile_gamma_one_adjacent_j_polynomial_1303a.ps1', 'compile_gamma_one_adjacent_j_polynomial_1303b.ps1', 'compile_gamma_one_adjacent_j_preservation_1305a.ps1', 'compile_gamma_one_adjacent_j_preservation_1305b.ps1', 'compile_gamma_one_adjacent_j_preservation_1305c.ps1', 'compile_gamma_one_adjacent_j_preservation_1305d.ps1', 'compile_gamma_one_adjacent_j_ratio_1299a.ps1', 'compile_gamma_one_adjacent_j_ratio_1299b.ps1', 'compile_gamma_one_adjacent_j_reverse_diamond_1317a.ps1', 'compile_gamma_one_adjacent_j_reverse_diamond_1317b.ps1', 'compile_gamma_one_adjacent_j_reverse_diamond_1317c.ps1', 'compile_gamma_one_adjacent_j_reverse_diamond_1317d.ps1', 'compile_gamma_one_adjacent_j_reverse_diamond_1317e.ps1', 'compile_gamma_one_coprime_generation_1298a.ps1', 'compile_gamma_one_embedding_census_1309a.ps1', 'compile_gamma_one_germ_faithfulness_1320a.ps1', 'compile_gamma_one_hecke_coordinate_degree_1295a.ps1', 'compile_gamma_one_hecke_diamond_norm_1319a.ps1', 'compile_gamma_one_hecke_diamond_norm_1319b.ps1', 'compile_gamma_one_hecke_integral_diamond_reduction_1323a.ps1', 'compile_gamma_one_hecke_integral_diamond_reduction_1323b.ps1', 'compile_gamma_one_hecke_integral_diamond_reduction_1323c.ps1', 'compile_gamma_one_hecke_prime_degree_1296a.ps1', 'compile_gamma_one_hecke_prime_degree_1296b.ps1', 'compile_gamma_one_hecke_prime_degree_1296c.ps1', 'compile_gamma_one_hecke_prime_degree_1296d.ps1', 'compile_gamma_one_mixed_laurent_reduction_1322a.ps1', 'compile_gamma_one_norm_embeddings_1308a.ps1', 'compile_gamma_one_norm_embeddings_1308b.ps1', 'compile_gamma_one_norm_product_1310a.ps1', 'compile_gamma_one_prime_hecke_index_1293a.ps1', 'compile_gamma_one_prime_hecke_index_1293b.ps1', 'compile_gamma_one_rational_analytic_germs_1314a.ps1', 'compile_gamma_one_rational_analytic_germs_1314b.ps1', 'compile_gamma_one_rational_analytic_germs_1314c.ps1', 'compile_gamma_one_realization_restriction_1300a.ps1', 'compile_gamma_one_signed_hecke_index_1294a.ps1', 'compile_gamma_one_upper_half_plane_hecke_germs_1315a.ps1', 'prepare_gamma_one_diamond_norm_audit_1321.py', 'prepare_gamma_one_diamond_norm_audit_1321b.py', 'prepare_gamma_one_diamond_reduction_audit_1325.py', 'prepare_gamma_one_hecke_degree_audit_1297.py', 'prepare_gamma_one_hecke_degree_audit_1297_generated.py', 'prepare_gamma_one_hecke_prime_degree_1296b.py', 'prepare_gamma_one_hecke_prime_degree_1296c.py', 'prepare_gamma_one_hecke_prime_degree_1296d.py', 'prepare_gamma_one_norm_audit_1311.py', 'prepare_gamma_one_norm_embeddings_1308.py', 'prepare_gamma_one_prime_hecke_index_1293b.py', 'record_gamma_one_diamond_norm_1321.py', 'record_gamma_one_diamond_norm_1321b.py', 'record_gamma_one_diamond_reduction_1325.py', 'record_gamma_one_hecke_degree_1297.py', 'record_gamma_one_norm_1311.py', 'source-gamma-one-diamond-norm-2-audit-config.json', 'source-gamma-one-diamond-norm-2-reuse-review-20261028.json', 'source-gamma-one-diamond-norm-2-scratch-receipt.json', 'source-gamma-one-diamond-norm-audit-route-1321.json', 'source-gamma-one-diamond-norm-audit-route-1321b.json', 'source-gamma-one-diamond-reduction-1-audit-config.json', 'source-gamma-one-diamond-reduction-1-reuse-review-20261028.json', 'source-gamma-one-diamond-reduction-1-scratch-receipt.json', 'source-gamma-one-diamond-reduction-audit-route-1325.json', 'source-gamma-one-hecke-degree-1-audit-config.json', 'source-gamma-one-hecke-degree-1-reuse-review-20261028.json', 'source-gamma-one-hecke-degree-1-scratch-receipt.json', 'source-gamma-one-hecke-degree-audit-route-1297.json', 'source-gamma-one-norm-1-audit-config.json', 'source-gamma-one-norm-1-reuse-review-20261028.json', 'source-gamma-one-norm-1-scratch-receipt.json', 'source-gamma-one-norm-audit-route-1311.json']]
for folder in ['gamma-one-hecke-prime-degree-1296a', 'gamma-one-hecke-prime-degree-1296b', 'gamma-one-hecke-prime-degree-1296c', 'gamma-one-prime-hecke-index-1293a']:
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
supplemental_review_path=r/archive_rel/'gamma-one-hecke-norm-promotion-route-1324.json'

audit = r / "Extension/Dubon2026/Audit.lean"
at = audit.read_text(encoding="utf-8")
for n in queries:
    assert not re.search(r"``" + re.escape(n) + r"(?=[,\s])", at)
tm, dm = "\n]\n\nprivate def publicConstructions", "\n]\n\nprivate def runAudit"
assert at.count(tm) == at.count(dm) == 1
at = at.replace(tm, "".join("\n  ,``" + n for n in theorems) + tm, 1)
at = at.replace(dm, "".join("\n  ," + chr(96)*2 + n for n in defs) + dm, 1)
research_path = r / "Tools/lean-reuse-audit-20261020.json"
reuse_path = r / "Tools/source-gamma-one-hecke-norm.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt9046"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> original Gamma1 arithmetic Hecke realization -> original Picard/Tate Frobenius and inertia -> actual Hecke norm reduction with the exact arithmetic diamond.'
discharged = 'For every nonzero level M and prime p coprime to M, the actual Gamma1 alpha extension has degree p+1. Native coprime subgroup reduction and analytic modular quotients prove adjacent-j nonmembership; the original correspondence field is exactly the lower field with j(q^p) adjoined. Its exact modular polynomial constructs a genuine reverse automorphism and the complete p+1 embedding census, giving the literal expanded norm. The exact integral matrix D_p gamma D_p/p identifies the reverse action on all original rational functions and descends to the actual arithmetic diamond. Its lower-right label d satisfies p*d=1 modulo M; no involution or Gamma0 diamond convention is assumed. On the original arithmetic field, w*alpha=beta and w*beta=alpha*diamond. The actual beta norm therefore has the precise twisted diamond product. With integral Laurent representatives of the input and its actual diamond image, that genuine norm is integral and its residue is coefficient Frobenius of the diamond image times q-to-q^p of the input. The norm product, reverse identity, embedding census and diamond label are derived, not supplied.'
boundary = 'An integral representative of the actual diamond image remains an explicit narrower input in the integral reduction theorem. Producing it from input integrality alone is required for unconditional integral norm reduction. Residue degree equality, genus preservation, compatible original-to-residue place/Picard specialization and prime-to-residue torsion injectivity remain; thus original geometric Tate Frobenius and inertia remain open. Parabolic character realization or a faithful alternative, exceptional primes, coefficient-field realization, original all-weight characteristic-zero association, local/image/regularity, automorphy and literal higher symmetric-power continuation remain. 16/20; DUB-17--20 OPEN; all twenty acceptance tests unchanged.'
status = 'The twenty-eight-module scope passes 85 public axiom queries, 141 exhaustive scratch theorem checks, sixteen linters per module and four declaration-value audits with 184 required dependency checks, with zero diagnostics. Production aggregate, focused audits and sequential foundation/paper verification of the 9,074-module scope are pending.'
route = 'Before expanding the dependency, reuse checks selected native coprime reduction, signed index and coordinate-degree identities, modular-ratio germs, cusp bounds, level-one polynomial classification and the rational prime-step theorem. The exact modular polynomial, original finite j-extension, tensor coefficient realization and existing Laurent conjugates avoid a new generator or automorphism framework. Existing analytic realization and arithmetic diamond descent identify the entire reverse action without extension to transcendental coefficient fields. The existing Laurent unexpansion and primitive-root reduction require only the two-input diamond adaptation. A kernel timeout was resolved using separate analytic/faithfulness lemmas and proved inclusion identities, without raising proof limits. The first diamond audit correctly rejected two Prop-valued instances misregistered as constructions; the successor registers their actual theorem kind and retains every check. Root pins, original objects and full acceptance criteria are unchanged. All promoted mathematical bodies and comments are identical to their audited forms after import qualification.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Original Gamma One Hecke degree, diamond and norm (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 9,046-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
corrections = []
count = sum(z['exhaustiveTheorems'] for z in certs)
assert count == 141

docpaths = list(dict.fromkeys(r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]))
for f in docpaths:
    assert "\n\n" in f.read_text(encoding="utf-8")
readmes = [(r.parent / "README.md", "Current Project 83 status ("), (repo / "README.md", "Project 83 has an ")]
for f, prefix in readmes:
    assert sum(line.startswith(prefix) for line in f.read_text(encoding="utf-8").splitlines()) == 1
arch = r / "Dubon Architecture.md"
edge = '  GAMMARED9046["Original coefficient valuation and residue field, regular prolongation, finite separating j-coordinate, arithmetic/Hecke residue maps, Frobenius factorization and exact residue-place orders proved. Degree equality, genus, norm identity, original Picard specialization, torsion injectivity and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourceGammaOneHeckeNormProductionAudit9074.lean',p/'source-gamma-one-hecke-norm-9074-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production9074.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/gamma-one-reduction-20261028-1292'
registered = {row['path'] for row in c['files']}
for priorFile in priorArchive.iterdir():
    rel = priorFile.relative_to(r).as_posix()
    if priorFile.is_file() and rel not in registered:
        c['files'].append({'path': rel, 'role': 'Tools'})

reportSource = p / 'Dubon Original Gamma One Hecke Norm Assessment 2026-10-28.md'
assert sha(reportSource) == '5F3B35708D392EF637FB3F847590F099A0BA4752E3353C8D119ED81E9B5251D3'
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
    "productionModules": 9074, "modules": newmods, "queries": queries,
    "theoremRegistrations": theorems, "constructionRegistrations": defs,
    "sourceHashes": {mapping[t.stem]: sha(t) for t, _ in pending}, "scratchCertificates": certs,
    "exactDependency": dependency, "assumptionsDischarged": discharged, "stillOpen": boundary,
    "status": status, "rootPinsChanged": False, "proofLimitsChanged": False,
    "promotionChanges": 'Only project scratch imports are qualified. All audited statements, proof bodies and comments remain identical. The original Gamma1 fields, all nonzero levels and coprime primes, the exact lower-right diamond label and the explicit integral diamond input are retained.',
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
arch.write_text(arch.read_text(encoding='utf-8').replace(edge,'  GAMMARED9046["Original coefficient valuation, residue field, arithmetic/Hecke maps, Frobenius factorization and residue-place orders proved (DUB-17/18)"] --> GAMMANORM9074\n  GAMMANORM9074["Original Gamma1 degree p+1, adjacent-j generation, reverse automorphism, exact arithmetic diamond and norm product proved. Integral norm reduction consumes an integral diamond representative. Diamond integrality, residue degree/genus, original Picard specialization, torsion injectivity and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'),encoding='utf-8')



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Original Gamma One Hecke degree, diamond and norm - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-gamma-one-hecke-norm.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub('  logInfo m!".*"\n', '  logInfo m!"SOURCE GAMMA ONE HECKE NORM AUDIT PASS: {count} theorems including private/generated declarations. Actual original degree, generation, embedding census, exact arithmetic diamond and norm product. Integral diamond input, degree/genus preservation, original Picard specialization and arithmetic realization remain;16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourceGammaOneHeckeNormProductionAudit9074.lean").write_text(out, encoding="utf-8")
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
    target = p / (source.stem + "Production9074.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
(p / "source-gamma-one-hecke-norm-9074-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 9074, "increment": 28, "queries": 85,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
