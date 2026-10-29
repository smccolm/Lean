from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 9074
assert d["appliedSourceGammaOneHeckeNorm"]["receipt9074"]["exit"] == 0
assert (p / "paper-verification-9074-console.exit").read_text().strip() == "0"
assert (r/'Tools/gamma-one-hecke-norm-20261028-1324/canonical-evidence-9074.json').exists()
key = "appliedSourceGammaOnePicardReduction"
assert key not in d
digests = {'source-gamma-one-specialization-1-scratch-receipt.json': 'B4A46110ECE61C258197939EFBDA9E048BACE84F19E216B553680831FAA53534', 'source-gamma-one-kummer-1-scratch-receipt.json': '74CFD24CC719EB59E16077D6011357656C1187F0F7796BE0283608F845F98BDF', 'source-gamma-one-gauss-norm-1-scratch-receipt.json': '63EACEEE6908866F27421952D186856D26BFC1A3BCA2BDFFE2F78EA14F668A55'}

for name, digest in digests.items():
    assert sha(p / name) == digest
certs = [json.loads((p / name).read_text(encoding="utf-8")) for name in digests]
mods = [m for z in certs for m in z["modules"]]
queries = [q for z in certs for q in z["queries"]]
theorems = [q for z in certs for q in z["theoremRegistrations"]]
defs = [q for z in certs for q in z["constructionRegistrations"]]
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (23, 23, 36, 33, 3)
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
archive_rel='Tools/gamma-one-picard-reduction-20261028-1358'
evidence=[p/'gamma-one-picard-reduction-promotion-route-1358.json']
evidence += [p/n for n in ['SourceCurveSeparatingGenusMaximum-1333.exit', 'SourceCurveSeparatingGenusMaximum-1333.log', 'SourceCurveSeparatingGenusMaximum.lean', 'SourceCurveSeparatingGenusMaximum1328a.exit', 'SourceCurveSeparatingGenusMaximum1328a.lean', 'SourceCurveSeparatingGenusMaximum1328a.log', 'SourceGammaOneDiamondGauss-1356.exit', 'SourceGammaOneDiamondGauss-1356.log', 'SourceGammaOneDiamondGauss.lean', 'SourceGammaOneDiamondGauss1351a.exit', 'SourceGammaOneDiamondGauss1351a.lean', 'SourceGammaOneDiamondGauss1351a.log', 'SourceGammaOneGaussNormAudit1.exit', 'SourceGammaOneGaussNormAudit1.lean', 'SourceGammaOneGaussNormAudit1.log', 'SourceGammaOneGaussNormDependencyAudit1.exit', 'SourceGammaOneGaussNormDependencyAudit1.lean', 'SourceGammaOneGaussNormDependencyAudit1.log', 'SourceGammaOneGaussNormScratchOwnership1357.exit', 'SourceGammaOneGaussNormScratchOwnership1357.lean', 'SourceGammaOneGaussNormScratchOwnership1357.log', 'SourceGammaOneGenusSpecialization-1333.exit', 'SourceGammaOneGenusSpecialization-1333.log', 'SourceGammaOneGenusSpecialization.lean', 'SourceGammaOneGenusSpecialization1331a.exit', 'SourceGammaOneGenusSpecialization1331a.lean.txt', 'SourceGammaOneGenusSpecialization1331a.log', 'SourceGammaOneGenusSpecialization1331b.exit', 'SourceGammaOneGenusSpecialization1331b.lean.txt', 'SourceGammaOneGenusSpecialization1331b.log', 'SourceGammaOneGenusSpecialization1331c.exit', 'SourceGammaOneGenusSpecialization1331c.lean.txt', 'SourceGammaOneGenusSpecialization1331c.log', 'SourceGammaOneGenusSpecialization1331d.exit', 'SourceGammaOneGenusSpecialization1331d.lean', 'SourceGammaOneGenusSpecialization1331d.log', 'SourceGammaOneHeckeFractionProduct-1356.exit', 'SourceGammaOneHeckeFractionProduct-1356.log', 'SourceGammaOneHeckeFractionProduct.lean', 'SourceGammaOneHeckeFractionProduct1353a.exit', 'SourceGammaOneHeckeFractionProduct1353a.lean.txt', 'SourceGammaOneHeckeFractionProduct1353a.log', 'SourceGammaOneHeckeFractionProduct1353b.exit', 'SourceGammaOneHeckeFractionProduct1353b.lean', 'SourceGammaOneHeckeFractionProduct1353b.log', 'SourceGammaOneHeckeGaussNorm-1356.exit', 'SourceGammaOneHeckeGaussNorm-1356.log', 'SourceGammaOneHeckeGaussNorm.lean', 'SourceGammaOneHeckeGaussNorm1354a.exit', 'SourceGammaOneHeckeGaussNorm1354a.lean.txt', 'SourceGammaOneHeckeGaussNorm1354a.log', 'SourceGammaOneHeckeGaussNorm1354b.exit', 'SourceGammaOneHeckeGaussNorm1354b.lean.txt', 'SourceGammaOneHeckeGaussNorm1354b.log', 'SourceGammaOneHeckeGaussNorm1354c.exit', 'SourceGammaOneHeckeGaussNorm1354c.lean', 'SourceGammaOneHeckeGaussNorm1354c.log', 'SourceGammaOneHeckeGaussReflection-1356.exit', 'SourceGammaOneHeckeGaussReflection-1356.log', 'SourceGammaOneHeckeGaussReflection.lean', 'SourceGammaOneHeckeGaussReflection1352a.exit', 'SourceGammaOneHeckeGaussReflection1352a.lean.txt', 'SourceGammaOneHeckeGaussReflection1352a.log', 'SourceGammaOneHeckeGaussReflection1352b.exit', 'SourceGammaOneHeckeGaussReflection1352b.lean.txt', 'SourceGammaOneHeckeGaussReflection1352b.log', 'SourceGammaOneHeckeGaussReflection1352c.exit', 'SourceGammaOneHeckeGaussReflection1352c.lean.txt', 'SourceGammaOneHeckeGaussReflection1352c.log', 'SourceGammaOneHeckeGaussReflection1352d.exit', 'SourceGammaOneHeckeGaussReflection1352d.lean.txt', 'SourceGammaOneHeckeGaussReflection1352d.log', 'SourceGammaOneHeckeGaussReflection1352e.exit', 'SourceGammaOneHeckeGaussReflection1352e.lean.txt', 'SourceGammaOneHeckeGaussReflection1352e.log', 'SourceGammaOneHeckeGaussReflection1352f.exit', 'SourceGammaOneHeckeGaussReflection1352f.lean', 'SourceGammaOneHeckeGaussReflection1352f.log', 'SourceGammaOneJointChartDimension1337a.exit', 'SourceGammaOneJointChartDimension1337a.lean.txt', 'SourceGammaOneJointChartDimension1337a.log', 'SourceGammaOneJointChartDimension1337b.exit', 'SourceGammaOneJointChartDimension1337b.lean.txt', 'SourceGammaOneJointChartDimension1337b.log', 'SourceGammaOneJointChartDimension1337c.exit', 'SourceGammaOneJointChartDimension1337c.lean.txt', 'SourceGammaOneJointChartDimension1337c.log', 'SourceGammaOneJointChartSpaces1339a.exit', 'SourceGammaOneJointChartSpaces1339a.lean.txt', 'SourceGammaOneJointChartSpaces1339a.log', 'SourceGammaOneKummerAudit1.exit', 'SourceGammaOneKummerAudit1.lean', 'SourceGammaOneKummerAudit1.log', 'SourceGammaOneKummerDegree-1348.exit', 'SourceGammaOneKummerDegree-1348.log', 'SourceGammaOneKummerDegree.lean', 'SourceGammaOneKummerDegree1335a.exit', 'SourceGammaOneKummerDegree1335a.lean', 'SourceGammaOneKummerDegree1335a.log', 'SourceGammaOneKummerDependencyAudit1.exit', 'SourceGammaOneKummerDependencyAudit1.lean', 'SourceGammaOneKummerDependencyAudit1.log', 'SourceGammaOneKummerGenus-1348.exit', 'SourceGammaOneKummerGenus-1348.log', 'SourceGammaOneKummerGenus.lean', 'SourceGammaOneKummerGenus1336a.exit', 'SourceGammaOneKummerGenus1336a.lean', 'SourceGammaOneKummerGenus1336a.log', 'SourceGammaOneKummerPowerLifting-1348.exit', 'SourceGammaOneKummerPowerLifting-1348.log', 'SourceGammaOneKummerPowerLifting.lean', 'SourceGammaOneKummerPowerLifting1344a.exit', 'SourceGammaOneKummerPowerLifting1344a.lean.txt', 'SourceGammaOneKummerPowerLifting1344a.log', 'SourceGammaOneKummerPowerLifting1344b.exit', 'SourceGammaOneKummerPowerLifting1344b.lean.txt', 'SourceGammaOneKummerPowerLifting1344b.log', 'SourceGammaOneKummerPowerLifting1344c.exit', 'SourceGammaOneKummerPowerLifting1344c.lean.txt', 'SourceGammaOneKummerPowerLifting1344c.log', 'SourceGammaOneKummerPowerLifting1344d.exit', 'SourceGammaOneKummerPowerLifting1344d.lean.txt', 'SourceGammaOneKummerPowerLifting1344d.log', 'SourceGammaOneKummerPowerLifting1347a.exit', 'SourceGammaOneKummerPowerLifting1347a.lean.txt', 'SourceGammaOneKummerPowerLifting1347a.log', 'SourceGammaOneKummerPowerLifting1347b.exit', 'SourceGammaOneKummerPowerLifting1347b.lean', 'SourceGammaOneKummerPowerLifting1347b.log', 'SourceGammaOneKummerResidueGenus-1348.exit', 'SourceGammaOneKummerResidueGenus-1348.log', 'SourceGammaOneKummerResidueGenus.lean', 'SourceGammaOneKummerResidueGenus1344e.exit', 'SourceGammaOneKummerResidueGenus1344e.lean', 'SourceGammaOneKummerResidueGenus1344e.log', 'SourceGammaOneKummerScratchOwnership1349.exit', 'SourceGammaOneKummerScratchOwnership1349.lean', 'SourceGammaOneKummerScratchOwnership1349.log', 'SourceGammaOneOriginalSpecialization-1333.exit', 'SourceGammaOneOriginalSpecialization-1333.log', 'SourceGammaOneOriginalSpecialization.lean', 'SourceGammaOneOriginalSpecialization1332a.exit', 'SourceGammaOneOriginalSpecialization1332a.lean.txt', 'SourceGammaOneOriginalSpecialization1332a.log', 'SourceGammaOneOriginalSpecialization1332b.exit', 'SourceGammaOneOriginalSpecialization1332b.lean', 'SourceGammaOneOriginalSpecialization1332b.log', 'SourceGammaOnePicardPrimeKernel-1348.exit', 'SourceGammaOnePicardPrimeKernel-1348.log', 'SourceGammaOnePicardPrimeKernel.lean', 'SourceGammaOnePicardPrimeKernel1345a.exit', 'SourceGammaOnePicardPrimeKernel1345a.lean.txt', 'SourceGammaOnePicardPrimeKernel1345a.log', 'SourceGammaOnePicardPrimeKernel1345b.exit', 'SourceGammaOnePicardPrimeKernel1345b.lean', 'SourceGammaOnePicardPrimeKernel1345b.log', 'SourceGammaOnePicardTorsion-1348.exit', 'SourceGammaOnePicardTorsion-1348.log', 'SourceGammaOnePicardTorsion.lean', 'SourceGammaOnePicardTorsion1346a.exit', 'SourceGammaOnePicardTorsion1346a.lean', 'SourceGammaOnePicardTorsion1346a.log', 'SourceGammaOneResidueGeometry-1333.exit', 'SourceGammaOneResidueGeometry-1333.log', 'SourceGammaOneResidueGeometry.lean', 'SourceGammaOneResidueGeometry1327a-run2.exit', 'SourceGammaOneResidueGeometry1327a-run2.log', 'SourceGammaOneResidueGeometry1327a-run3.exit', 'SourceGammaOneResidueGeometry1327a-run3.log', 'SourceGammaOneResidueGeometry1327a.exit', 'SourceGammaOneResidueGeometry1327a.lean.txt', 'SourceGammaOneResidueGeometry1327a.log', 'SourceGammaOneResidueGeometry1327b.exit', 'SourceGammaOneResidueGeometry1327b.lean', 'SourceGammaOneResidueGeometry1327b.log', 'SourceGammaOneSpecializationAudit1.exit', 'SourceGammaOneSpecializationAudit1.lean', 'SourceGammaOneSpecializationAudit1.log', 'SourceGammaOneSpecializationDependencyAudit1.exit', 'SourceGammaOneSpecializationDependencyAudit1.lean', 'SourceGammaOneSpecializationDependencyAudit1.log', 'SourceGammaOneSpecializationScratchOwnership1334.exit', 'SourceGammaOneSpecializationScratchOwnership1334.lean', 'SourceGammaOneSpecializationScratchOwnership1334.log', 'SourceJointSeparableChartDimension-1348.exit', 'SourceJointSeparableChartDimension-1348.log', 'SourceJointSeparableChartDimension.lean', 'SourceJointSeparableChartDimension1341a.exit', 'SourceJointSeparableChartDimension1341a.lean', 'SourceJointSeparableChartDimension1341a.log', 'SourceJointSeparableConstants-1348.exit', 'SourceJointSeparableConstants-1348.log', 'SourceJointSeparableConstants.lean', 'SourceJointSeparableConstants1340a.exit', 'SourceJointSeparableConstants1340a.lean.txt', 'SourceJointSeparableConstants1340a.log', 'SourceJointSeparableConstants1340b.exit', 'SourceJointSeparableConstants1340b.lean', 'SourceJointSeparableConstants1340b.log', 'SourceJointSeparableFiniteOverlap-1348.exit', 'SourceJointSeparableFiniteOverlap-1348.log', 'SourceJointSeparableFiniteOverlap.lean', 'SourceJointSeparableFiniteOverlap1338a.exit', 'SourceJointSeparableFiniteOverlap1338a.lean', 'SourceJointSeparableFiniteOverlap1338a.log', 'SourceJointSeparableGenus-1348.exit', 'SourceJointSeparableGenus-1348.log', 'SourceJointSeparableGenus.lean', 'SourceJointSeparableGenus1343a.exit', 'SourceJointSeparableGenus1343a.lean', 'SourceJointSeparableGenus1343a.log', 'SourceJointSeparablePoleDimension-1348.exit', 'SourceJointSeparablePoleDimension-1348.log', 'SourceJointSeparablePoleDimension.lean', 'SourceJointSeparablePoleDimension1342a.exit', 'SourceJointSeparablePoleDimension1342a.lean.txt', 'SourceJointSeparablePoleDimension1342a.log', 'SourceJointSeparablePoleDimension1342b.exit', 'SourceJointSeparablePoleDimension1342b.lean', 'SourceJointSeparablePoleDimension1342b.log', 'SourceReductionCoordinateAutomorphism-1356.exit', 'SourceReductionCoordinateAutomorphism-1356.log', 'SourceReductionCoordinateAutomorphism.lean', 'SourceReductionCoordinateAutomorphism1350a.exit', 'SourceReductionCoordinateAutomorphism1350a.lean.txt', 'SourceReductionCoordinateAutomorphism1350a.log', 'SourceReductionCoordinateAutomorphism1350b.exit', 'SourceReductionCoordinateAutomorphism1350b.lean', 'SourceReductionCoordinateAutomorphism1350b.log', 'SourceReductionGenusIntegralCharts-1333.exit', 'SourceReductionGenusIntegralCharts-1333.log', 'SourceReductionGenusIntegralCharts.lean', 'SourceReductionGenusIntegralCharts1330a.exit', 'SourceReductionGenusIntegralCharts1330a.lean.txt', 'SourceReductionGenusIntegralCharts1330a.log', 'SourceReductionGenusIntegralCharts1330b.exit', 'SourceReductionGenusIntegralCharts1330b.lean.txt', 'SourceReductionGenusIntegralCharts1330b.log', 'SourceReductionGenusIntegralCharts1330c.exit', 'SourceReductionGenusIntegralCharts1330c.lean', 'SourceReductionGenusIntegralCharts1330c.log', 'SourceReductionGenusPoleLifting-1333.exit', 'SourceReductionGenusPoleLifting-1333.log', 'SourceReductionGenusPoleLifting.lean', 'SourceReductionGenusPoleLifting1329a.exit', 'SourceReductionGenusPoleLifting1329a.lean.txt', 'SourceReductionGenusPoleLifting1329a.log', 'SourceReductionGenusPoleLifting1329b.exit', 'SourceReductionGenusPoleLifting1329b.lean.txt', 'SourceReductionGenusPoleLifting1329b.log', 'SourceReductionGenusPoleLifting1329c.exit', 'SourceReductionGenusPoleLifting1329c.lean', 'SourceReductionGenusPoleLifting1329c.log', 'SourceReductionMapReflection-1356.exit', 'SourceReductionMapReflection-1356.log', 'SourceReductionMapReflection.lean', 'SourceReductionMapReflection1355a.exit', 'SourceReductionMapReflection1355a.lean', 'SourceReductionMapReflection1355a.log', 'audit_gamma_one_gauss_norm_1357.ps1', 'audit_gamma_one_kummer_1349.ps1', 'audit_gamma_one_specialization_1334.ps1', 'build_gamma_one_gauss_norm_1354.ps1', 'build_gamma_one_gauss_norm_1354b.ps1', 'build_gamma_one_gauss_norm_1354c.ps1', 'build_gamma_one_gauss_norm_1354d.ps1', 'build_gamma_one_gauss_norm_1356.ps1', 'build_gamma_one_kummer_1348.ps1', 'build_gamma_one_kummer_consumers_1347.ps1', 'build_gamma_one_kummer_consumers_1347b.ps1', 'build_gamma_one_picard_consumers_1345b.ps1', 'build_gamma_one_specialization_1333.ps1', 'classification1330a-focus.log', 'classification1330b-focus.log', 'classification1330c-focus.log', 'classification1330d-focus.log', 'classification1330e-focus.log', 'classification1340a-focus.log', 'classification1340b-focus.log', 'classification1340c-focus.log', 'classification1340d-focus.log', 'consumers1330-focus.log', 'consumers1330.txt', 'consumers1338.txt', 'consumers1340-focus.log', 'consumers1340.txt', 'consumers1348.txt', 'consumers1349-focus.log', 'consumers1349.txt', 'docs1330.py', 'docs1340.py', 'docs1349.py', 'foundation1330-console.log', 'foundation1340-console.log', 'foundation1340b-console.log', 'foundation1349-console.log', 'gamma-one-gauss-norm-versions-1356.json', 'gamma-one-kummer-versions-1348.json', 'gamma-one-route-review-1326.md', 'gamma-one-specialization-versions-1333.json', 'induced1349a-focus.log', 'induced1349b-focus.log', 'induced1349c-focus.log', 'induced1349d-focus.log', 'math1330.txt', 'math1338.txt', 'math1340.txt', 'math1348.txt', 'math1349.txt', 'modules1330.json', 'modules1338-draft.json', 'modules1340-draft.json', 'modules1340.json', 'modules1348-draft.json', 'modules1349-draft.json', 'modules1349.json', 'paper1330-console.log', 'paper1340-console.log', 'paper1349-console.log', 'prepare_coordinate_aut_retry_1350b.py', 'prepare_fraction_product_retry_1353b.py', 'prepare_gamma_one_gauss_norm_1356.py', 'prepare_gamma_one_gauss_norm_audit_1357.py', 'prepare_gamma_one_kummer_1348.py', 'prepare_gamma_one_kummer_audit_1349.py', 'prepare_gamma_one_specialization_1333.py', 'prepare_gamma_one_specialization_audit_1334.py', 'prepare_gauss_norm_retry_1354b.py', 'prepare_gauss_norm_retry_1354c.py', 'prepare_gauss_reflection_retry_1352b.py', 'prepare_gauss_reflection_retry_1352c.py', 'prepare_gauss_reflection_retry_1352d.py', 'prepare_gauss_reflection_retry_1352e.py', 'prepare_gauss_reflection_retry_1352f.py', 'prepare_joint_retry_1341.py', 'prepare_kummer_split_1344e.py', 'prepare_pole_retry_1342b.py', 'prepare_power_retry_1344b.py', 'prepare_power_retry_1344c.py', 'prepare_power_retry_1344d.py', 'prepare_power_retry_1347b.py', 'prepare_prime_kernel_retry_1345b.py', 'record1330.py', 'record1340.py', 'record1349.py', 'record_gamma_one_gauss_norm_1357.py', 'record_gamma_one_kummer_1349.py', 'record_gamma_one_specialization_1334.py', 'register1330.py', 'register1338.py', 'register1340.py', 'register1349.py', 'registrations1330.json', 'registrations1340.json', 'registrations1349.json', 'remaining1330.txt', 'remaining1338.txt', 'remaining1340.txt', 'remaining1348.txt', 'remaining1349.txt', 'section1330.txt', 'section1340.txt', 'section1349.txt', 'source-gamma-one-gauss-norm-1-audit-config.json', 'source-gamma-one-gauss-norm-1-reuse-review-20261028.json', 'source-gamma-one-gauss-norm-1-scratch-receipt.json', 'source-gamma-one-gauss-norm-audit-route-1357.json', 'source-gamma-one-kummer-1-audit-config.json', 'source-gamma-one-kummer-1-reuse-review-20261028.json', 'source-gamma-one-kummer-1-scratch-receipt.json', 'source-gamma-one-kummer-audit-route-1349.json', 'source-gamma-one-specialization-1-audit-config.json', 'source-gamma-one-specialization-1-reuse-review-20261028.json', 'source-gamma-one-specialization-1-scratch-receipt.json', 'source-gamma-one-specialization-audit-route-1334.json', 'status1330.txt', 'status1340.txt', 'status1349.txt']]
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
supplemental_review_path=r/archive_rel/'gamma-one-picard-reduction-promotion-route-1358.json'

audit = r / "Extension/Dubon2026/Audit.lean"
at = audit.read_text(encoding="utf-8")
for n in queries:
    assert not re.search(r"``" + re.escape(n) + r"(?=[,\s])", at)
tm, dm = "\n]\n\nprivate def publicConstructions", "\n]\n\nprivate def runAudit"
assert at.count(tm) == at.count(dm) == 1
at = at.replace(tm, "".join("\n  ,``" + n for n in theorems) + tm, 1)
at = at.replace(dm, "".join("\n  ," + chr(96)*2 + n for n in defs) + dm, 1)
research_path = r / "Tools/lean-reuse-audit-20261020.json"
reuse_path = r / "Tools/source-gamma-one-picard-reduction.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt9074"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> original finite Gamma1 Hecke-character realization -> actual Picard/H1/Tate realization with Frobenius and inertia -> original coefficient specialization, torsion injectivity and exact Hecke norm reduction.'
discharged = 'On the actual original Gamma1 coefficient field and its coefficient residue image, equality of j-coordinate degrees and equality of the actual adelic genera imply a degree-preserving specialization compatible with every principal divisor and injective on every torsion subgroup whose order is invertible in the residue field. Separating coordinates supply the residue curve structure; pole-space dimensions supply integral chart lifts. Native Kummer covers and their genus formula derive power lifting and Picard torsion injectivity, including the required common-constant and finite-overlap arguments. Separately, coordinate-degree equality alone implies that the actual arithmetic diamond preserves the coefficient Gauss ring. The actual beta embedding reflects Gauss integrality. Integral fraction witnesses then give Gauss integrality and the exact residue formula for the original Hecke norm: coefficient Frobenius of the arithmetic diamond image times q-to-q^p of the input. No coefficientwise integral Laurent representative of the diamond image is assumed or claimed. Place specialization, torsion injectivity, diamond Gauss integrality and the norm residue formula are derived from the displayed narrower geometric inputs.'
boundary = 'Actual Gamma1 j-coordinate degree equality and actual genus preservation remain open; this scope is conditional on those geometric equalities. Original norm/place/Picard compatibility and the geometric Tate Frobenius and inertia comparison remain. The Hecke correspondence at the residue prime cannot be assigned good reduction merely from good reduction of its base. Parabolic character realization or a faithful alternative, exceptional primes, coefficient-field realization, original all-weight characteristic-zero association, local/image/regularity, automorphy and literal higher symmetric-power continuation remain. Acceptance stays 16/20; DUB-17--20 OPEN; all twenty acceptance tests are unchanged.'
status = 'The twenty-three-module scope passes 36 public axiom queries, 51 exhaustive scratch theorem checks, sixteen linters per module and three declaration-value audits with 97 required dependency checks, with zero diagnostics. Production aggregate, focused audits and sequential foundation/paper verification of the 9,097-module scope are pending.'
route = 'The fresh upstream review and native reuse search were checked before expanding these dependencies. Native separating-coordinate Riemann--Roch, regular prolongation, integral chart gluing, Kummer degree/unramifiedness and genus formulas, valuation-ring integral closedness, original Hecke norm products and Laurent fraction witnesses are reused. Coordinate-degree equality makes valuation integers integral over the fixed coordinate intersection, so arithmetic diamond Gauss preservation follows without a new valuation uniqueness or curve-model framework. Fraction witnesses avoid the stronger and unnecessary coefficientwise integral-diamond premise. Generic reflection and joint-coordinate lemmas replace expensive concrete instance elaboration; failed attempts remain inert evidence, and no proof limit is raised. A finite-exceptional-prime shortcut was rejected because restoring omitted good-prime Euler factors would require independent local bounds, whereas the present purity theorem depends on full continuation. No prime range, original object, root pin or acceptance condition changes. Promoted mathematical bodies and comments are identical to their audited forms after import qualification.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Original Gamma One specialization, torsion and Gauss norm (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 9,074-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
corrections = []
count = sum(z['exhaustiveTheorems'] for z in certs)
assert count == 51

docpaths = list(dict.fromkeys(r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]))
for f in docpaths:
    assert "\n\n" in f.read_text(encoding="utf-8")
readmes = [(r.parent / "README.md", "Current Project 83 status ("), (repo / "README.md", "Project 83 has an ")]
for f, prefix in readmes:
    assert sum(line.startswith(prefix) for line in f.read_text(encoding="utf-8").splitlines()) == 1
arch = r / "Dubon Architecture.md"
edge = '  GAMMANORM9074["Original Gamma1 degree p+1, adjacent-j generation, reverse automorphism, exact arithmetic diamond and norm product proved. Integral norm reduction consumes an integral diamond representative. Diamond integrality, residue degree/genus, original Picard specialization, torsion injectivity and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourceGammaOnePicardReductionProductionAudit9097.lean',p/'source-gamma-one-picard-reduction-9097-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production9097.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/gamma-one-hecke-norm-20261028-1324'
registered = {row['path'] for row in c['files']}
for priorFile in priorArchive.iterdir():
    rel = priorFile.relative_to(r).as_posix()
    if priorFile.is_file() and rel not in registered:
        c['files'].append({'path': rel, 'role': 'Tools'})

reportSource = p / 'Dubon Original Gamma One Picard Reduction Assessment 2026-10-28.md'
assert sha(reportSource) == 'B9CC628D1F1A864245BDAB3ECAB9465121F174C785FA00D06150352D40287A14'
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
    "productionModules": 9097, "modules": newmods, "queries": queries,
    "theoremRegistrations": theorems, "constructionRegistrations": defs,
    "sourceHashes": {mapping[t.stem]: sha(t) for t, _ in pending}, "scratchCertificates": certs,
    "exactDependency": dependency, "assumptionsDischarged": discharged, "stillOpen": boundary,
    "status": status, "rootPinsChanged": False, "proofLimitsChanged": False,
    "promotionChanges": 'Only project scratch imports are qualified. All audited statements, proof bodies and comments remain identical. The original Gamma1 fields, coefficient Gauss rings, exact arithmetic diamond, every invertible torsion order, and the explicit coordinate-degree and genus hypotheses are retained.',
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
arch.write_text(arch.read_text(encoding='utf-8').replace(edge,'  GAMMANORM9074["Original Gamma1 degree p+1, adjacent-j generation, reverse automorphism, exact arithmetic diamond and norm product proved (DUB-17/18)"] --> GAMMAPICARD9097\n  GAMMAPICARD9097["Original specialization and invertible-torsion injectivity from coordinate-degree/genus equality; diamond Gauss preservation and exact norm residue from coordinate-degree equality. Actual degree/genus, norm/place/Picard compatibility, Tate Frobenius/inertia and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'),encoding='utf-8')



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Original Gamma One specialization, torsion and Gauss norm - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-gamma-one-picard-reduction.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub('  logInfo m!".*"\n', '  logInfo m!"SOURCE GAMMA ONE PICARD REDUCTION AUDIT PASS: {count} theorems including private/generated declarations. Actual original specialization and torsion injectivity from coordinate-degree/genus equality; diamond Gauss preservation and exact norm residue from degree equality. Actual geometric equalities, norm/place/Picard compatibility and arithmetic realization remain;16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourceGammaOnePicardReductionProductionAudit9097.lean").write_text(out, encoding="utf-8")
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
    target = p / (source.stem + "Production9097.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
(p / "source-gamma-one-picard-reduction-9097-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 9097, "increment": 23, "queries": 36,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
