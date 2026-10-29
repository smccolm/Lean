from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 9097
assert d["appliedSourceGammaOnePicardReduction"]["receipt9097"]["exit"] == 0
assert (p / "paper-verification-9097-console.exit").read_text().strip() == "0"
assert (r/'Tools/gamma-one-picard-reduction-20261028-1358/canonical-evidence-9097.json').exists()
key = "appliedSourceGammaOneTateFrobenius"
assert key not in d
digests = {'source-gamma-one-inertia-1-scratch-receipt.json': '10C46E538883A340E91B64DD1BD9CA1F635DD8EFF28ED2D97EFA5A125266FEC6', 'source-gamma-one-frobenius-1-scratch-receipt.json': '8F25CF0241B3A41B12110108432520EA36FCF85BE8F5FD554E6FA71D764D2469', 'source-gamma-one-arithmetic-1-scratch-receipt.json': 'F7A5DDC14EF57EBFEFDDBE07EEC36F2D4F79CB66357E1CD4379BBA7E1DA787AE'}

for name, digest in digests.items():
    assert sha(p / name) == digest
certs = [json.loads((p / name).read_text(encoding="utf-8")) for name in digests]
mods = [m for z in certs for m in z["modules"]]
queries = [q for z in certs for q in z["queries"]]
theorems = [q for z in certs for q in z["theoremRegistrations"]]
defs = [q for z in certs for q in z["constructionRegistrations"]]
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (26, 26, 49, 45, 4)
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
archive_rel='Tools/gamma-one-tate-frobenius-20261028-1402'
evidence=[p/'gamma-one-tate-frobenius-promotion-route-1402.json']
evidence += [p/n for n in ['HomogeneousDiagonalAction-verified1375.lean', 'HomogeneousDimension-verified1375.lean', 'HomogeneousMonomialBasis-verified1375.lean', 'Inspect1367.lean', 'MatrixPolynomialAction-verified1375.lean', 'Preflight1397.lean', 'SourceGammaOneArithmeticAudit1.exit', 'SourceGammaOneArithmeticAudit1.lean', 'SourceGammaOneArithmeticAudit1.log', 'SourceGammaOneArithmeticCharts-1367.exit', 'SourceGammaOneArithmeticCharts-1367.log', 'SourceGammaOneArithmeticCharts.lean', 'SourceGammaOneArithmeticCharts1359a.exit', 'SourceGammaOneArithmeticCharts1359a.lean', 'SourceGammaOneArithmeticCharts1359a.log', 'SourceGammaOneArithmeticDependencyAudit1.exit', 'SourceGammaOneArithmeticDependencyAudit1.lean', 'SourceGammaOneArithmeticDependencyAudit1.log', 'SourceGammaOneArithmeticFrobenius-1396.exit', 'SourceGammaOneArithmeticFrobenius-1396.log', 'SourceGammaOneArithmeticFrobenius.lean', 'SourceGammaOneArithmeticFrobenius1392a.exit', 'SourceGammaOneArithmeticFrobenius1392a.lean.txt', 'SourceGammaOneArithmeticFrobenius1392a.log', 'SourceGammaOneArithmeticFrobenius1392b.exit', 'SourceGammaOneArithmeticFrobenius1392b.lean.txt', 'SourceGammaOneArithmeticFrobenius1392b.log', 'SourceGammaOneArithmeticFrobenius1392c.exit', 'SourceGammaOneArithmeticFrobenius1392c.lean.txt', 'SourceGammaOneArithmeticFrobenius1392c.log', 'SourceGammaOneArithmeticFrobenius1392d.exit', 'SourceGammaOneArithmeticFrobenius1392d.lean', 'SourceGammaOneArithmeticFrobenius1392d.log', 'SourceGammaOneArithmeticScratchOwnership1397.exit', 'SourceGammaOneArithmeticScratchOwnership1397.lean', 'SourceGammaOneArithmeticScratchOwnership1397.log', 'SourceGammaOneCoefficientFrobenius1386a.exit', 'SourceGammaOneCoefficientFrobenius1386a.lean.txt', 'SourceGammaOneCoefficientFrobenius1386a.log', 'SourceGammaOneComplementaryDiamond1385a.exit', 'SourceGammaOneComplementaryDiamond1385a.lean.txt', 'SourceGammaOneComplementaryDiamond1385a.log', 'SourceGammaOneConstantReductionCharts-1367.exit', 'SourceGammaOneConstantReductionCharts-1367.log', 'SourceGammaOneConstantReductionCharts.lean', 'SourceGammaOneConstantReductionCharts1362a.exit', 'SourceGammaOneConstantReductionCharts1362a.lean', 'SourceGammaOneConstantReductionCharts1362a.log', 'SourceGammaOneDecompositionCharts-1367.exit', 'SourceGammaOneDecompositionCharts-1367.log', 'SourceGammaOneDecompositionCharts.lean', 'SourceGammaOneDecompositionCharts1361a.exit', 'SourceGammaOneDecompositionCharts1361a.lean.txt', 'SourceGammaOneDecompositionCharts1361a.log', 'SourceGammaOneDecompositionCharts1361b.exit', 'SourceGammaOneDecompositionCharts1361b.lean', 'SourceGammaOneDecompositionCharts1361b.log', 'SourceGammaOneFrobeniusAudit1.exit', 'SourceGammaOneFrobeniusAudit1.lean', 'SourceGammaOneFrobeniusAudit1.log', 'SourceGammaOneFrobeniusDependencyAudit1.exit', 'SourceGammaOneFrobeniusDependencyAudit1.lean', 'SourceGammaOneFrobeniusDependencyAudit1.log', 'SourceGammaOneFrobeniusScratchOwnership1395.exit', 'SourceGammaOneFrobeniusScratchOwnership1395.lean', 'SourceGammaOneFrobeniusScratchOwnership1395.log', 'SourceGammaOneGeometricArithmeticFrobenius-1396.exit', 'SourceGammaOneGeometricArithmeticFrobenius-1396.log', 'SourceGammaOneGeometricArithmeticFrobenius.lean', 'SourceGammaOneGeometricArithmeticFrobenius1393a.lean.txt', 'SourceGammaOneGeometricArithmeticFrobenius1393b.exit', 'SourceGammaOneGeometricArithmeticFrobenius1393b.lean.txt', 'SourceGammaOneGeometricArithmeticFrobenius1393b.log', 'SourceGammaOneGeometricArithmeticFrobenius1393c.exit', 'SourceGammaOneGeometricArithmeticFrobenius1393c.lean', 'SourceGammaOneGeometricArithmeticFrobenius1393c.log', 'SourceGammaOneGeometricCoefficientFrobenius1388a.lean.txt', 'SourceGammaOneHeckeIntegralAgreement-1394.exit', 'SourceGammaOneHeckeIntegralAgreement-1394.log', 'SourceGammaOneHeckeIntegralAgreement.lean', 'SourceGammaOneHeckeIntegralAgreement1373a.exit', 'SourceGammaOneHeckeIntegralAgreement1373a.lean', 'SourceGammaOneHeckeIntegralAgreement1373a.log', 'SourceGammaOneHeckePicardDescent-1394.exit', 'SourceGammaOneHeckePicardDescent-1394.log', 'SourceGammaOneHeckePicardDescent.lean', 'SourceGammaOneHeckePicardDescent1381a.exit', 'SourceGammaOneHeckePicardDescent1381a.lean.txt', 'SourceGammaOneHeckePicardDescent1381a.log', 'SourceGammaOneHeckePicardDescent1381b-diagnostics.exit', 'SourceGammaOneHeckePicardDescent1381b-diagnostics.log', 'SourceGammaOneHeckePicardDescent1381b.exit', 'SourceGammaOneHeckePicardDescent1381b.lean.txt', 'SourceGammaOneHeckePicardDescent1381b.log', 'SourceGammaOneHeckePicardDescent1381c.exit', 'SourceGammaOneHeckePicardDescent1381c.lean.txt', 'SourceGammaOneHeckePicardDescent1381c.log', 'SourceGammaOneHeckePicardDescent1381d.exit', 'SourceGammaOneHeckePicardDescent1381d.lean.txt', 'SourceGammaOneHeckePicardDescent1381d.log', 'SourceGammaOneHeckePicardDescent1381e.exit', 'SourceGammaOneHeckePicardDescent1381e.lean.txt', 'SourceGammaOneHeckePicardDescent1381e.log', 'SourceGammaOneHeckePicardDescent1381f.exit', 'SourceGammaOneHeckePicardDescent1381f.lean', 'SourceGammaOneHeckePicardDescent1381f.log', 'SourceGammaOneHeckePrincipalNorm-1394.exit', 'SourceGammaOneHeckePrincipalNorm-1394.log', 'SourceGammaOneHeckePrincipalNorm.lean', 'SourceGammaOneHeckePrincipalNorm1369a.exit', 'SourceGammaOneHeckePrincipalNorm1369a.lean.txt', 'SourceGammaOneHeckePrincipalNorm1369a.log', 'SourceGammaOneHeckePrincipalNorm1369b.exit', 'SourceGammaOneHeckePrincipalNorm1369b.lean', 'SourceGammaOneHeckePrincipalNorm1369b.log', 'SourceGammaOneHeckeResidueNorm-1394.exit', 'SourceGammaOneHeckeResidueNorm-1394.log', 'SourceGammaOneHeckeResidueNorm.lean', 'SourceGammaOneHeckeResidueNorm1371a.exit', 'SourceGammaOneHeckeResidueNorm1371a.lean', 'SourceGammaOneHeckeResidueNorm1371a.log', 'SourceGammaOneHeckeTorsionDivisors-1394.exit', 'SourceGammaOneHeckeTorsionDivisors-1394.log', 'SourceGammaOneHeckeTorsionDivisors.lean', 'SourceGammaOneHeckeTorsionDivisors1374a.exit', 'SourceGammaOneHeckeTorsionDivisors1374a.lean', 'SourceGammaOneHeckeTorsionDivisors1374a.log', 'SourceGammaOneHeckeTorsionPicard-1394.exit', 'SourceGammaOneHeckeTorsionPicard-1394.log', 'SourceGammaOneHeckeTorsionPicard.lean', 'SourceGammaOneHeckeTorsionPicard1378a.lean.txt', 'SourceGammaOneHeckeTorsionPicard1378b.exit', 'SourceGammaOneHeckeTorsionPicard1378b.lean.txt', 'SourceGammaOneHeckeTorsionPicard1378b.log', 'SourceGammaOneHeckeTorsionPicard1378c.exit', 'SourceGammaOneHeckeTorsionPicard1378c.lean.txt', 'SourceGammaOneHeckeTorsionPicard1378c.log', 'SourceGammaOneHeckeTorsionPicard1378d.lean.txt', 'SourceGammaOneHeckeTorsionPicard1378e.lean.txt', 'SourceGammaOneHeckeTorsionPicard1378f.exit', 'SourceGammaOneHeckeTorsionPicard1378f.lean.txt', 'SourceGammaOneHeckeTorsionPicard1378f.log', 'SourceGammaOneHeckeTorsionPicard1378g.exit', 'SourceGammaOneHeckeTorsionPicard1378g.lean.txt', 'SourceGammaOneHeckeTorsionPicard1378g.log', 'SourceGammaOneHeckeTorsionPicard1378h.exit', 'SourceGammaOneHeckeTorsionPicard1378h.lean', 'SourceGammaOneHeckeTorsionPicard1378h.log', 'SourceGammaOneInertiaAudit1.exit', 'SourceGammaOneInertiaAudit1.lean', 'SourceGammaOneInertiaAudit1.log', 'SourceGammaOneInertiaDependencyAudit1.exit', 'SourceGammaOneInertiaDependencyAudit1.lean', 'SourceGammaOneInertiaDependencyAudit1.log', 'SourceGammaOneInertiaPicard-1367.exit', 'SourceGammaOneInertiaPicard-1367.log', 'SourceGammaOneInertiaPicard.lean', 'SourceGammaOneInertiaPicard1365a.lean.txt', 'SourceGammaOneInertiaPicard1365b.exit', 'SourceGammaOneInertiaPicard1365b.lean.txt', 'SourceGammaOneInertiaPicard1365b.log', 'SourceGammaOneInertiaPicard1365c.exit', 'SourceGammaOneInertiaPicard1365c.lean', 'SourceGammaOneInertiaPicard1365c.log', 'SourceGammaOneInertiaPlaceReduction-1367.exit', 'SourceGammaOneInertiaPlaceReduction-1367.log', 'SourceGammaOneInertiaPlaceReduction.lean', 'SourceGammaOneInertiaPlaceReduction1364a.exit', 'SourceGammaOneInertiaPlaceReduction1364a.lean.txt', 'SourceGammaOneInertiaPlaceReduction1364a.log', 'SourceGammaOneInertiaPlaceReduction1364b.exit', 'SourceGammaOneInertiaPlaceReduction1364b.lean', 'SourceGammaOneInertiaPlaceReduction1364b.log', 'SourceGammaOneInertiaScratchOwnership1368.exit', 'SourceGammaOneInertiaScratchOwnership1368.lean', 'SourceGammaOneInertiaScratchOwnership1368.log', 'SourceGammaOneIntegralDivisorReduction-1394.exit', 'SourceGammaOneIntegralDivisorReduction-1394.log', 'SourceGammaOneIntegralDivisorReduction.lean', 'SourceGammaOneIntegralDivisorReduction1372a.exit', 'SourceGammaOneIntegralDivisorReduction1372a.lean', 'SourceGammaOneIntegralDivisorReduction1372a.log', 'SourceGammaOneNormDiamondOrientation-1394.exit', 'SourceGammaOneNormDiamondOrientation-1394.log', 'SourceGammaOneNormDiamondOrientation.lean', 'SourceGammaOneNormDiamondOrientation1377a.exit', 'SourceGammaOneNormDiamondOrientation1377a.lean.txt', 'SourceGammaOneNormDiamondOrientation1377a.log', 'SourceGammaOneNormDiamondOrientation1377b.exit', 'SourceGammaOneNormDiamondOrientation1377b.lean', 'SourceGammaOneNormDiamondOrientation1377b.log', 'SourceGammaOnePicardFrobeniusRelation-1394.exit', 'SourceGammaOnePicardFrobeniusRelation-1394.log', 'SourceGammaOnePicardFrobeniusRelation.lean', 'SourceGammaOnePicardFrobeniusRelation1379a.lean.txt', 'SourceGammaOnePicardFrobeniusRelation1379b.lean.txt', 'SourceGammaOnePicardFrobeniusRelation1379c.lean.txt', 'SourceGammaOnePicardFrobeniusRelation1379d.lean.txt', 'SourceGammaOnePicardFrobeniusRelation1379e.lean.txt', 'SourceGammaOnePicardFrobeniusRelation1379f.lean.txt', 'SourceGammaOnePicardFrobeniusRelation1379g.lean.txt', 'SourceGammaOnePicardFrobeniusRelation1379h.exit', 'SourceGammaOnePicardFrobeniusRelation1379h.lean.txt', 'SourceGammaOnePicardFrobeniusRelation1379h.log', 'SourceGammaOnePicardFrobeniusRelation1379i.exit', 'SourceGammaOnePicardFrobeniusRelation1379i.lean.txt', 'SourceGammaOnePicardFrobeniusRelation1379i.log', 'SourceGammaOnePicardFrobeniusRelation1379j.exit', 'SourceGammaOnePicardFrobeniusRelation1379j.lean.txt', 'SourceGammaOnePicardFrobeniusRelation1379j.log', 'SourceGammaOnePicardFrobeniusRelation1379k.exit', 'SourceGammaOnePicardFrobeniusRelation1379k.lean.txt', 'SourceGammaOnePicardFrobeniusRelation1379k.log', 'SourceGammaOnePicardFrobeniusRelation1379l.exit', 'SourceGammaOnePicardFrobeniusRelation1379l.lean.txt', 'SourceGammaOnePicardFrobeniusRelation1379l.log', 'SourceGammaOnePicardFrobeniusRelation1379m.lean.txt', 'SourceGammaOnePicardFrobeniusRelation1379n.exit', 'SourceGammaOnePicardFrobeniusRelation1379n.lean', 'SourceGammaOnePicardFrobeniusRelation1379n.log', 'SourceGammaOneReductionPicardEquivariance-1394.exit', 'SourceGammaOneReductionPicardEquivariance-1394.log', 'SourceGammaOneReductionPicardEquivariance.lean', 'SourceGammaOneReductionPicardEquivariance1376a.exit', 'SourceGammaOneReductionPicardEquivariance1376a.lean.txt', 'SourceGammaOneReductionPicardEquivariance1376a.log', 'SourceGammaOneReductionPicardEquivariance1376b.exit', 'SourceGammaOneReductionPicardEquivariance1376b.lean.txt', 'SourceGammaOneReductionPicardEquivariance1376b.log', 'SourceGammaOneReductionPicardEquivariance1376c.exit', 'SourceGammaOneReductionPicardEquivariance1376c.lean', 'SourceGammaOneReductionPicardEquivariance1376c.log', 'SourceGammaOneResidueDivisors-1394.exit', 'SourceGammaOneResidueDivisors-1394.log', 'SourceGammaOneResidueDivisors.lean', 'SourceGammaOneResidueDivisors1370a.exit', 'SourceGammaOneResidueDivisors1370a.lean', 'SourceGammaOneResidueDivisors1370a.log', 'SourceGammaOneResiduePicard-1394.exit', 'SourceGammaOneResiduePicard-1394.log', 'SourceGammaOneResiduePicard.lean', 'SourceGammaOneResiduePicard1375a.exit', 'SourceGammaOneResiduePicard1375a.lean', 'SourceGammaOneResiduePicard1375a.log', 'SourceGammaOneSpecializationCharts-1367.exit', 'SourceGammaOneSpecializationCharts-1367.log', 'SourceGammaOneSpecializationCharts.lean', 'SourceGammaOneSpecializationCharts1360a.exit', 'SourceGammaOneSpecializationCharts1360a.lean', 'SourceGammaOneSpecializationCharts1360a.log', 'SourceGammaOneSpecializationEquivariance-1367.exit', 'SourceGammaOneSpecializationEquivariance-1367.log', 'SourceGammaOneSpecializationEquivariance.lean', 'SourceGammaOneSpecializationEquivariance1363a.lean.txt', 'SourceGammaOneSpecializationEquivariance1363b.exit', 'SourceGammaOneSpecializationEquivariance1363b.lean', 'SourceGammaOneSpecializationEquivariance1363b.log', 'SourceGammaOneTateFrobeniusRelation-1394.exit', 'SourceGammaOneTateFrobeniusRelation-1394.log', 'SourceGammaOneTateFrobeniusRelation.lean', 'SourceGammaOneTateFrobeniusRelation1380a.lean.txt', 'SourceGammaOneTateFrobeniusRelation1380b.lean.txt', 'SourceGammaOneTateFrobeniusRelation1380c.lean.txt', 'SourceGammaOneTateFrobeniusRelation1380d.lean.txt', 'SourceGammaOneTateFrobeniusRelation1380e.lean.txt', 'SourceGammaOneTateFrobeniusRelation1380f.lean.txt', 'SourceGammaOneTateFrobeniusRelation1380g.lean.txt', 'SourceGammaOneTateFrobeniusRelation1380h.lean.txt', 'SourceGammaOneTateFrobeniusRelation1380i.lean.txt', 'SourceGammaOneTateFrobeniusRelation1380j.exit', 'SourceGammaOneTateFrobeniusRelation1380j.lean.txt', 'SourceGammaOneTateFrobeniusRelation1380j.log', 'SourceGammaOneTateFrobeniusRelation1380k.exit', 'SourceGammaOneTateFrobeniusRelation1380k.lean.txt', 'SourceGammaOneTateFrobeniusRelation1380k.log', 'SourceGammaOneTateFrobeniusRelation1380l.exit', 'SourceGammaOneTateFrobeniusRelation1380l.lean.txt', 'SourceGammaOneTateFrobeniusRelation1380l.log', 'SourceGammaOneTateFrobeniusRelation1380m.exit', 'SourceGammaOneTateFrobeniusRelation1380m.lean.txt', 'SourceGammaOneTateFrobeniusRelation1380m.log', 'SourceGammaOneTateFrobeniusRelation1380n.exit', 'SourceGammaOneTateFrobeniusRelation1380n.lean', 'SourceGammaOneTateFrobeniusRelation1380n.log', 'SourceGammaOneTateInertia-1367.exit', 'SourceGammaOneTateInertia-1367.log', 'SourceGammaOneTateInertia.lean', 'SourceGammaOneTateInertia1366a.lean.txt', 'SourceGammaOneTateInertia1366b.lean.txt', 'SourceGammaOneTateInertia1366c.exit', 'SourceGammaOneTateInertia1366c.lean', 'SourceGammaOneTateInertia1366c.log', 'SourceHomogeneousComplementaryHecke1384a.exit', 'SourceHomogeneousComplementaryHecke1384a.lean.txt', 'SourceHomogeneousComplementaryHecke1384a.log', 'SourceTateDualArithmeticQuadratic-1396.exit', 'SourceTateDualArithmeticQuadratic-1396.log', 'SourceTateDualArithmeticQuadratic.lean', 'SourceTateDualArithmeticQuadratic1391a.exit', 'SourceTateDualArithmeticQuadratic1391a.lean', 'SourceTateDualArithmeticQuadratic1391a.log', 'SourceTateDualDiamondQuadratic1383a.exit', 'SourceTateDualDiamondQuadratic1383a.lean.txt', 'SourceTateDualDiamondQuadratic1383a.log', 'SourceTateTorsionQuadratic-1394.exit', 'SourceTateTorsionQuadratic-1394.log', 'SourceTateTorsionQuadratic.lean', 'SourceTateTorsionQuadratic1390a.exit', 'SourceTateTorsionQuadratic1390a.lean', 'SourceTateTorsionQuadratic1390a.log', 'SourceTorsionReductionDiamond-1394.exit', 'SourceTorsionReductionDiamond-1394.log', 'SourceTorsionReductionDiamond.lean', 'SourceTorsionReductionDiamond1389a.exit', 'SourceTorsionReductionDiamond1389a.lean.txt', 'SourceTorsionReductionDiamond1389a.log', 'SourceTorsionReductionDiamond1389b.exit', 'SourceTorsionReductionDiamond1389b.lean', 'SourceTorsionReductionDiamond1389b.log', 'UniversalMatrixPolynomial-verified1375.lean', 'arithmetic1380a-focus.log', 'arithmetic1380b-focus.log', 'arithmetic1380c-focus.log', 'arithmetic1380d-focus.log', 'arithmetic1380e-focus.log', 'arithmetic1380f-focus.log', 'arithmetic1380g-focus.log', 'arithmetic1380h-focus.log', 'arithmetic1380i-focus.log', 'arithmetic1380j-focus.log', 'arithmetic1380k-focus.log', 'audit_gamma_one_arithmetic_1397.ps1', 'audit_gamma_one_frobenius_1395.ps1', 'audit_gamma_one_inertia_1368.ps1', 'build_gamma_one_arithmetic_canonical_1396.ps1', 'build_gamma_one_arithmetic_frobenius_1392.ps1', 'build_gamma_one_arithmetic_frobenius_1392b.ps1', 'build_gamma_one_arithmetic_frobenius_1392c.ps1', 'build_gamma_one_arithmetic_frobenius_1392d.ps1', 'build_gamma_one_chart_transport_1361.ps1', 'build_gamma_one_chart_transport_1361b.ps1', 'build_gamma_one_coefficient_frobenius_1386.ps1', 'build_gamma_one_complementary_1384.ps1', 'build_gamma_one_frobenius_canonical_1394.ps1', 'build_gamma_one_frobenius_consumers_1382.ps1', 'build_gamma_one_frobenius_consumers_1387.ps1', 'build_gamma_one_frobenius_divisors_1369.ps1', 'build_gamma_one_frobenius_field_1379i.ps1', 'build_gamma_one_frobenius_field_1379j.ps1', 'build_gamma_one_frobenius_norm_1371.ps1', 'build_gamma_one_geometric_arithmetic_1393.ps1', 'build_gamma_one_geometric_arithmetic_1393b.ps1', 'build_gamma_one_geometric_arithmetic_1393c.ps1', 'build_gamma_one_hecke_integral_agreement_1372.ps1', 'build_gamma_one_hecke_torsion_1374.ps1', 'build_gamma_one_inertia_1359.ps1', 'build_gamma_one_inertia_canonical_1367.ps1', 'build_gamma_one_picard_actions_1376.ps1', 'build_gamma_one_picard_actions_1376b.ps1', 'build_gamma_one_picard_actions_1376c.ps1', 'build_gamma_one_picard_descent_1378c.ps1', 'build_gamma_one_picard_descent_1381.ps1', 'build_gamma_one_picard_descent_1381b.ps1', 'build_gamma_one_picard_descent_1381c.ps1', 'build_gamma_one_picard_descent_1381d.ps1', 'build_gamma_one_picard_descent_1381e.ps1', 'build_gamma_one_picard_descent_1381f.ps1', 'build_gamma_one_picard_frobenius_1377b.ps1', 'build_gamma_one_picard_frobenius_1378.ps1', 'build_gamma_one_picard_frobenius_1378b.ps1', 'build_gamma_one_picard_relation_1379k.ps1', 'build_gamma_one_picard_relation_1379m.ps1', 'build_gamma_one_picard_relation_1389b.ps1', 'build_gamma_one_tate_inertia_1364.ps1', 'build_gamma_one_tate_inertia_1364b.ps1', 'build_gamma_one_tate_inertia_1365c.ps1', 'build_gamma_one_tate_relation_1380n.ps1', 'build_gamma_one_tate_relation_1390.ps1', 'build_gamma_one_torsion_picard_1378h.ps1', 'coefficient1367a-focus.log', 'coefficient1367b-focus.log', 'coefficient1367c-focus.log', 'coefficient1367d-focus.log', 'coefficient1367e-focus.log', 'coefficient1367f-focus.log', 'coefficient1367g-focus.log', 'coefficient1367h-focus.log', 'coefficient1367i-focus.log', 'coefficient1367j-focus.log', 'coefficient1367k-focus.log', 'coefficient1367l-focus.log', 'coefficient1367m-focus.log', 'coefficient1367n-focus.log', 'coefficient1367o-focus.log', 'consumers1367-focus.log', 'consumers1367.txt', 'consumers1375-focus.log', 'consumers1375.txt', 'consumers1380.txt', 'consumers1380a-focus.log', 'consumers1380b-focus.log', 'consumers1389-focus.log', 'consumers1389.txt', 'consumers1393-focus.log', 'consumers1393.txt', 'consumers1393b-focus.log', 'consumers1397-focus.log', 'consumers1397.txt', 'deformation1397-focus.log', 'deformation1397b-focus.log', 'deformation1397c-focus.log', 'deformation1397d-focus.log', 'deformation1397e-focus.log', 'determinant1389a-focus.log', 'determinant1389b-focus.log', 'determinant1389c-focus.log', 'determinant1389d-focus.log', 'determinant1389e-focus.log', 'determinant1389f-focus.log', 'determinant1389g-focus.log', 'diagnose_gamma_one_picard_descent_1381b.ps1', 'diagnose_gamma_one_picard_descent_1381d.py', 'diagnose_gamma_one_picard_relation_1379l.ps1', 'diagnose_gamma_one_picard_relation_1379l.py', 'diagnose_gamma_one_tate_relation_1380l.ps1', 'diagnose_gamma_one_tate_relation_1380l.py', 'diagnose_gamma_one_tate_relation_1380m.ps1', 'diagnose_gamma_one_tate_relation_1380m.py', 'diagnose_gamma_one_torsion_picard_1378g.ps1', 'diagnose_gamma_one_torsion_picard_1378g.py', 'docs1367.py', 'docs1371.py', 'docs1375.py', 'docs1380.py', 'docs1387.py', 'docs1389.py', 'docs1393.py', 'docs1397.py', 'foundation1367-console.log', 'foundation1375-console.log', 'foundation1380-console.log', 'foundation1389-console.log', 'foundation1393-console.log', 'foundation1397-console.log', 'gamma-one-arithmetic-frobenius-route-1393.json', 'gamma-one-arithmetic-versions-1396.json', 'gamma-one-frobenius-divisor-route-1369.json', 'gamma-one-frobenius-versions-1394.json', 'gamma-one-inertia-route-1359.json', 'gamma-one-inertia-versions-1367.json', 'inspect1367.log', 'math1367.txt', 'math1371.txt', 'math1375.txt', 'math1380.txt', 'math1387.txt', 'math1389.txt', 'math1393.txt', 'math1397.txt', 'modules1367-draft.json', 'modules1367.json', 'modules1375.json', 'modules1380.json', 'modules1387.json', 'modules1389.json', 'modules1393.json', 'modules1397.json', 'natural1393a-focus.log', 'natural1393b-focus.log', 'paper1367-console.log', 'paper1375-console.log', 'paper1380-console.log', 'paper1389-console.log', 'paper1393-console.log', 'paper1397-console.log', 'preflight1397.log', 'prepare1367.py', 'prepare1371.py', 'prepare1375.py', 'prepare1380.py', 'prepare1387.py', 'prepare1389.py', 'prepare1393.py', 'prepare1397.py', 'prepare_gamma_one_arithmetic_audit_1397.py', 'prepare_gamma_one_arithmetic_canonical_1396.py', 'prepare_gamma_one_arithmetic_frobenius_1392.py', 'prepare_gamma_one_chart_transport_1361.py', 'prepare_gamma_one_coefficient_frobenius_1386.py', 'prepare_gamma_one_complementary_1384.py', 'prepare_gamma_one_frobenius_audit_1395.py', 'prepare_gamma_one_frobenius_canonical_1394.py', 'prepare_gamma_one_frobenius_consumers_1382.py', 'prepare_gamma_one_frobenius_consumers_1387.py', 'prepare_gamma_one_frobenius_divisors_1369.py', 'prepare_gamma_one_frobenius_norm_1371.py', 'prepare_gamma_one_geometric_arithmetic_1393.py', 'prepare_gamma_one_hecke_integral_agreement_1372.py', 'prepare_gamma_one_hecke_torsion_1374.py', 'prepare_gamma_one_inertia_1359.py', 'prepare_gamma_one_inertia_audit_1368.py', 'prepare_gamma_one_inertia_canonical_1367.py', 'prepare_gamma_one_picard_actions_1376.py', 'prepare_gamma_one_picard_frobenius_1378.py', 'prepare_gamma_one_tate_inertia_1364.py', 'primary-review1375.json', 'primary-review1380.json', 'primary-review1387.json', 'primary-review1389.json', 'primary-review1393.json', 'primary-review1397.json', 'quotient1375a-focus.log', 'quotient1375b-focus.log', 'quotient1375c-focus.log', 'quotient1375d-focus.log', 'quotient1375e-focus.log', 'quotient1375f-focus.log', 'record1367.py', 'record1371.py', 'record1375.py', 'record1380.py', 'record1387.py', 'record1389.py', 'record1393.py', 'record1397.py', 'record_gamma_one_arithmetic_1397.py', 'record_gamma_one_frobenius_1395.py', 'record_gamma_one_inertia_1368.py', 'register1367.py', 'register1371.py', 'register1375.py', 'register1380.py', 'register1387.py', 'register1389.py', 'register1393.py', 'register1397.py', 'registrations1367.json', 'registrations1375.json', 'registrations1380.json', 'registrations1389.json', 'registrations1393.json', 'registrations1397.json', 'remaining1367.txt', 'remaining1371.txt', 'remaining1375.txt', 'remaining1380.txt', 'remaining1387.txt', 'remaining1389.txt', 'remaining1393.txt', 'remaining1397.txt', 'revise_gamma_one_arithmetic_frobenius_1392b.py', 'revise_gamma_one_arithmetic_frobenius_1392c.py', 'revise_gamma_one_arithmetic_frobenius_1392d.py', 'revise_gamma_one_chart_transport_1361b.py', 'revise_gamma_one_frobenius_field_1379i.py', 'revise_gamma_one_frobenius_field_1379j.py', 'revise_gamma_one_geometric_arithmetic_1393b.py', 'revise_gamma_one_geometric_arithmetic_1393c.py', 'revise_gamma_one_picard_actions_1376b.py', 'revise_gamma_one_picard_actions_1376c.py', 'revise_gamma_one_picard_descent_1378c.py', 'revise_gamma_one_picard_descent_1381b.py', 'revise_gamma_one_picard_descent_1381c.py', 'revise_gamma_one_picard_descent_1381e.py', 'revise_gamma_one_picard_descent_1381f.py', 'revise_gamma_one_picard_frobenius_1377b.py', 'revise_gamma_one_picard_relation_1379k.py', 'revise_gamma_one_picard_relation_1379m.py', 'revise_gamma_one_picard_relation_1389b.py', 'revise_gamma_one_tate_inertia_1364b.py', 'revise_gamma_one_tate_inertia_1365c.py', 'revise_gamma_one_tate_relation_1380n.py', 'revise_gamma_one_tate_relation_1390.py', 'revise_gamma_one_torsion_picard_1378h.py', 'section1367.txt', 'section1375.txt', 'section1380.txt', 'section1389.txt', 'section1393.txt', 'section1397.txt', 'source-gamma-one-arithmetic-1-audit-config.json', 'source-gamma-one-arithmetic-1-reuse-review-20261028.json', 'source-gamma-one-arithmetic-1-scratch-receipt.json', 'source-gamma-one-arithmetic-audit-route-1397.json', 'source-gamma-one-frobenius-1-audit-config.json', 'source-gamma-one-frobenius-1-reuse-review-20261028.json', 'source-gamma-one-frobenius-1-scratch-receipt.json', 'source-gamma-one-frobenius-audit-route-1395.json', 'source-gamma-one-inertia-1-audit-config.json', 'source-gamma-one-inertia-1-reuse-review-20261028.json', 'source-gamma-one-inertia-1-scratch-receipt.json', 'source-gamma-one-inertia-audit-route-1368.json', 'split_gamma_one_picard_descent_1381.py', 'status1367.txt', 'status1375.txt', 'status1380.txt', 'status1389.txt', 'status1393.txt', 'status1397.txt']]
for folder in []:
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
supplemental_review_path=r/archive_rel/'gamma-one-tate-frobenius-promotion-route-1402.json'

audit = r / "Extension/Dubon2026/Audit.lean"
at = audit.read_text(encoding="utf-8")
for n in queries:
    assert not re.search(r"``" + re.escape(n) + r"(?=[,\s])", at)
tm, dm = "\n]\n\nprivate def publicConstructions", "\n]\n\nprivate def runAudit"
assert at.count(tm) == at.count(dm) == 1
at = at.replace(tm, "".join("\n  ,``" + n for n in theorems) + tm, 1)
at = at.replace(dm, "".join("\n  ," + chr(96)*2 + n for n in defs) + dm, 1)
research_path = r / "Tools/lean-reuse-audit-20261020.json"
reuse_path = r / "Tools/source-gamma-one-tate-frobenius.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt9097"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> original finite Gamma1 Hecke-character realization -> actual Picard/H1/Tate realization with Frobenius and inertia -> original equivariant specialization, torsion injection and exact norm-derived Tate relations.'
discharged = 'For the actual original Gamma1 coefficient field and its residue image, coordinate-degree equality and genus equality now imply inertia triviality on every Tate module with residue-invertible coefficient prime. The same constructed specialization is decomposition-equivariant and injective on invertible Picard torsion. The literal Hecke principal norm, its residue formula and torsion-free divisor cancellation give exact compatibility on finite Picard torsion, without a good-reduction model of the upper Hecke correspondence. Equivariance and injectivity then derive the original Tate identity H*F = F*F*D + p, where F is coefficient arithmetic Frobenius and the Picard diamond D has label p. The inverse label in the field norm is identified explicitly with the original Picard convention. On the actual homogeneous-valued Tate dual with combined-diamond fixedness, inverse Frobenius, the existing Hecke coefficient matrix and one cyclotomic factor give Y*Hdual = Y^2 + p^(w+1) in every weight. The final consumer derives its Tate identity from the original norm and specialization; it does not assume a Frobenius quadratic.'
boundary = 'Actual Gamma1 j-coordinate degree equality and actual genus preservation remain open. The Frobenius and inertia statements remain conditional on those narrower geometric inputs. Combined-diamond fixedness, genuine global finite Galois/Hecke-character realization, parabolic character realization or a faithful alternative, exceptional primes, coefficient-field realization, original all-weight characteristic-zero association, local/image/regularity, automorphy and literal higher symmetric-power continuation remain. The newly derived twisted coefficient relation does not silently discharge the earlier differently normalized conditional relation. Acceptance stays 16/20; DUB-17--20 OPEN; all twenty acceptance tests are unchanged.'
status = 'The twenty-six-module scope passes 49 public axiom queries, 81 exhaustive scratch theorem checks, sixteen linters per module and three declaration-value audits with 99 required dependency checks, with zero diagnostics. Production aggregate, focused audits and sequential foundation/paper verification of the 9,123-module scope are pending.'
route = 'The fresh upstream review and native reuse search were checked before expansion. Native regular-prolongation chart specialization, Kummer torsion injectivity, correspondence principal norms, primitive constant normalization, integer-divisor cancellation, Picard quotients, Tate functor and homogeneous Hecke-diamond identities are reused. The norm route avoids an unnecessary good-reduction model of the upper correspondence. Explicit additive maps and narrow torsion functor consumers resolve expensive concrete elaboration without raising proof limits. A complementary-coefficient normalization was compiled, then deferred when inverse Frobenius with the existing coefficient matrix supplied a shorter route to a genuine dual Galois action. Deferred and failed source versions remain inert evidence and are not promoted or counted. No prime range, original object, root pin, source convention or acceptance condition changes. Promoted mathematical bodies and comments are identical to their audited forms after import qualification.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Original Gamma One inertia and Tate Frobenius (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 9,097-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
corrections = []
count = sum(z['exhaustiveTheorems'] for z in certs)
assert count == 81

docpaths = list(dict.fromkeys(r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]))
for f in docpaths:
    assert "\n\n" in f.read_text(encoding="utf-8")
readmes = [(r.parent / "README.md", "Current Project 83 status ("), (repo / "README.md", "Project 83 has an ")]
for f, prefix in readmes:
    assert sum(line.startswith(prefix) for line in f.read_text(encoding="utf-8").splitlines()) == 1
arch = r / "Dubon Architecture.md"
edge = '  GAMMAPICARD9097["Original specialization and invertible-torsion injectivity from coordinate-degree/genus equality; diamond Gauss preservation and exact norm residue from coordinate-degree equality. Actual degree/genus, norm/place/Picard compatibility, Tate Frobenius/inertia and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourceGammaOneTateFrobeniusProductionAudit9123.lean',p/'source-gamma-one-tate-frobenius-9123-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production9123.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/gamma-one-picard-reduction-20261028-1358'
registered = {row['path'] for row in c['files']}
for priorFile in priorArchive.iterdir():
    rel = priorFile.relative_to(r).as_posix()
    if priorFile.is_file() and rel not in registered:
        c['files'].append({'path': rel, 'role': 'Tools'})

reportSource = p / 'Dubon Original Gamma One Tate Frobenius Assessment 2026-10-28.md'
assert sha(reportSource) == '009DF13557E33646F620A67431F3A9DE84DE1BE44A35B89420F5A5EA66F2BF84'
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
    "productionModules": 9123, "modules": newmods, "queries": queries,
    "theoremRegistrations": theorems, "constructionRegistrations": defs,
    "sourceHashes": {mapping[t.stem]: sha(t) for t, _ in pending}, "scratchCertificates": certs,
    "exactDependency": dependency, "assumptionsDischarged": discharged, "stillOpen": boundary,
    "status": status, "rootPinsChanged": False, "proofLimitsChanged": False,
    "promotionChanges": 'Only project scratch imports are qualified. All audited statements, proof bodies and comments remain identical. The original Gamma1 fields, literal norm and diamond conventions, every residue-invertible Tate prime, every homogeneous weight, and the explicit coordinate-degree and genus hypotheses are retained.',
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
arch.write_text(arch.read_text(encoding='utf-8').replace(edge,'  GAMMAPICARD9097["Original specialization and invertible-torsion injection from degree/genus equality; diamond Gauss preservation and exact norm residue derived (DUB-17/18)"] --> GAMMATATE9123\n  GAMMATATE9123["Original Gamma1 inertia and norm-derived Tate Frobenius from degree/genus equality; inverse-action homogeneous polynomial derived on combined-diamond fixed part. Actual degree/genus, global Galois/character realization and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'),encoding='utf-8')



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Original Gamma One inertia and Tate Frobenius - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-gamma-one-tate-frobenius.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub('  logInfo m!".*"\n', '  logInfo m!"SOURCE GAMMA ONE TATE FROBENIUS AUDIT PASS: {count} theorems including private/generated declarations. Actual original inertia and norm-derived twisted Tate Frobenius from coordinate-degree/genus equality; inverse-action all-weight polynomial on the combined-diamond fixed dual. Actual geometric equalities and global arithmetic/character realization remain;16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourceGammaOneTateFrobeniusProductionAudit9123.lean").write_text(out, encoding="utf-8")
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
    target = p / (source.stem + "Production9123.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
(p / "source-gamma-one-tate-frobenius-9123-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 9123, "increment": 26, "queries": 49,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
