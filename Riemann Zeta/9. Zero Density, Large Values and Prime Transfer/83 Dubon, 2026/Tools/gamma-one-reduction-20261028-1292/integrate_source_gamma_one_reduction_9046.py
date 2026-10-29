from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 9026
assert d["appliedSourceFrobeniusDiamond"]["receipt9026"]["exit"] == 0
assert (p / "paper-verification-9026-console.exit").read_text().strip() == "0"
assert (r/'Tools/frobenius-diamond-20261028-1267/canonical-evidence-9026.json').exists()
key = "appliedSourceGammaOneReduction"
assert key not in d
digests = {'source-gamma-one-reduction-2-scratch-receipt.json': '9BE462BC9A8BFBC620D65095601BA44D299B59A8DE983A9FE23901F866165CB2', 'source-gamma-one-residue-compatibility-1-scratch-receipt.json': 'B10F72B14FABC7ACABF2EE142C35D6264C99E9586342E4D451E5EA657F538C76', 'source-gamma-one-residue-frobenius-1-scratch-receipt.json': '8A95510D121F635B14FBAC329DF0E66D3A6DAA0538C66CFF6242866CD00A18C0', 'source-gamma-one-residue-places-1-scratch-receipt.json': '298499191235ABA610A23E4651D52E24D565B8C406234F4D1E6A6EED0307E0DD'}

for name, digest in digests.items():
    assert sha(p / name) == digest
certs = [json.loads((p / name).read_text(encoding="utf-8")) for name in digests]
mods = [m for z in certs for m in z["modules"]]
queries = [q for z in certs for q in z["queries"]]
theorems = [q for z in certs for q in z["theoremRegistrations"]]
defs = [q for z in certs for q in z["constructionRegistrations"]]
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (20, 20, 91, 71, 20)
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
archive_rel='Tools/gamma-one-reduction-20261028-1292'
evidence=[p/'gamma-one-reduction-promotion-route-1292.json']
evidence += [p/n for n in ['SourceGammaOneDecompositionGauss.lean', 'SourceGammaOneDecompositionGauss1280a.exit', 'SourceGammaOneDecompositionGauss1280a.log', 'SourceGammaOneGaussConstants.lean', 'SourceGammaOneGaussConstants1272a.exit', 'SourceGammaOneGaussConstants1272a.log', 'SourceGammaOneGaussCriterion.lean', 'SourceGammaOneGaussCriterion1268a.exit', 'SourceGammaOneGaussCriterion1268a.log', 'SourceGammaOneGaussCriterion1268b.exit', 'SourceGammaOneGaussCriterion1268b.log', 'SourceGammaOneGaussResidueHom.lean', 'SourceGammaOneGaussResidueHom1270a.exit', 'SourceGammaOneGaussResidueHom1270a.log', 'SourceGammaOneGaussResidueHom1270b.exit', 'SourceGammaOneGaussResidueHom1270b.log', 'SourceGammaOneGaussResidueImage.lean', 'SourceGammaOneGaussResidueImage1273a.exit', 'SourceGammaOneGaussResidueImage1273a.log', 'SourceGammaOneGaussResidueImage1273b.exit', 'SourceGammaOneGaussResidueImage1273b.log', 'SourceGammaOneGaussResidueKernel.lean', 'SourceGammaOneGaussResidueKernel1271a.exit', 'SourceGammaOneGaussResidueKernel1271a.log', 'SourceGammaOneGaussValuation.lean', 'SourceGammaOneGaussValuation1269a.exit', 'SourceGammaOneGaussValuation1269a.log', 'SourceGammaOneGaussValuation1269b.exit', 'SourceGammaOneGaussValuation1269b.log', 'SourceGammaOneHeckeGauss.lean', 'SourceGammaOneHeckeGauss1281a.exit', 'SourceGammaOneHeckeGauss1281a.log', 'SourceGammaOneHeckeGauss1281b.exit', 'SourceGammaOneHeckeGauss1281b.log', 'SourceGammaOneReductionAudit2.exit', 'SourceGammaOneReductionAudit2.lean', 'SourceGammaOneReductionAudit2.log', 'SourceGammaOneReductionDependencyAudit2.exit', 'SourceGammaOneReductionDependencyAudit2.lean', 'SourceGammaOneReductionDependencyAudit2.log', 'SourceGammaOneReductionScratchOwnership1278.lean', 'SourceGammaOneReductionScratchOwnership1278b.exit', 'SourceGammaOneReductionScratchOwnership1278b.lean', 'SourceGammaOneReductionScratchOwnership1278b.log', 'SourceGammaOneRegularProlongation.lean', 'SourceGammaOneRegularProlongation1274a.exit', 'SourceGammaOneRegularProlongation1274a.log', 'SourceGammaOneResidueArithmetic.lean', 'SourceGammaOneResidueArithmetic1280a.exit', 'SourceGammaOneResidueArithmetic1280a.log', 'SourceGammaOneResidueCompatibilityAudit1.exit', 'SourceGammaOneResidueCompatibilityAudit1.lean', 'SourceGammaOneResidueCompatibilityAudit1.log', 'SourceGammaOneResidueCompatibilityDependencyAudit1.exit', 'SourceGammaOneResidueCompatibilityDependencyAudit1.lean', 'SourceGammaOneResidueCompatibilityDependencyAudit1.log', 'SourceGammaOneResidueCompatibilityScratchOwnership1285.exit', 'SourceGammaOneResidueCompatibilityScratchOwnership1285.lean', 'SourceGammaOneResidueCompatibilityScratchOwnership1285.log', 'SourceGammaOneResidueCoordinateFinite.lean', 'SourceGammaOneResidueCoordinateFinite1277a.exit', 'SourceGammaOneResidueCoordinateFinite1277a.log', 'SourceGammaOneResidueCoordinateFinite1277b.exit', 'SourceGammaOneResidueCoordinateFinite1277b.log', 'SourceGammaOneResidueFrobenius.lean', 'SourceGammaOneResidueFrobenius1286a.exit', 'SourceGammaOneResidueFrobenius1286a.log', 'SourceGammaOneResidueFrobenius1286b.exit', 'SourceGammaOneResidueFrobenius1286b.log', 'SourceGammaOneResidueFrobenius1286c.exit', 'SourceGammaOneResidueFrobenius1286c.log', 'SourceGammaOneResidueFrobenius1286d.exit', 'SourceGammaOneResidueFrobenius1286d.log', 'SourceGammaOneResidueFrobeniusAudit1.exit', 'SourceGammaOneResidueFrobeniusAudit1.lean', 'SourceGammaOneResidueFrobeniusAudit1.log', 'SourceGammaOneResidueFrobeniusDependencyAudit1.exit', 'SourceGammaOneResidueFrobeniusDependencyAudit1.lean', 'SourceGammaOneResidueFrobeniusDependencyAudit1.log', 'SourceGammaOneResidueFrobeniusPlaces.lean', 'SourceGammaOneResidueFrobeniusPlaces1290a.exit', 'SourceGammaOneResidueFrobeniusPlaces1290a.log', 'SourceGammaOneResidueFrobeniusScratchOwnership1287.exit', 'SourceGammaOneResidueFrobeniusScratchOwnership1287.lean', 'SourceGammaOneResidueFrobeniusScratchOwnership1287.log', 'SourceGammaOneResidueHecke.lean', 'SourceGammaOneResidueHecke1281b.exit', 'SourceGammaOneResidueHecke1281b.log', 'SourceGammaOneResidueHeckeFinite.lean', 'SourceGammaOneResidueHeckeFinite1282a.exit', 'SourceGammaOneResidueHeckeFinite1282a.log', 'SourceGammaOneResidueJCoordinate.lean', 'SourceGammaOneResidueJCoordinate1275a.exit', 'SourceGammaOneResidueJCoordinate1275a.log', 'SourceGammaOneResiduePlaceOrders.lean', 'SourceGammaOneResiduePlaceOrders1289a.exit', 'SourceGammaOneResiduePlaceOrders1289a.log', 'SourceGammaOneResiduePlaces.lean', 'SourceGammaOneResiduePlaces1288a.exit', 'SourceGammaOneResiduePlaces1288a.log', 'SourceGammaOneResiduePlacesAudit1.exit', 'SourceGammaOneResiduePlacesAudit1.lean', 'SourceGammaOneResiduePlacesAudit1.log', 'SourceGammaOneResiduePlacesDependencyAudit1.exit', 'SourceGammaOneResiduePlacesDependencyAudit1.lean', 'SourceGammaOneResiduePlacesDependencyAudit1.log', 'SourceGammaOneResiduePlacesScratchOwnership1291.exit', 'SourceGammaOneResiduePlacesScratchOwnership1291.lean', 'SourceGammaOneResiduePlacesScratchOwnership1291.log', 'SourceGammaOneResidueSeparability.lean', 'SourceGammaOneResidueSeparability1279a.exit', 'SourceGammaOneResidueSeparability1279a.log', 'SourceGammaOneResidueSeparability1279b.exit', 'SourceGammaOneResidueSeparability1279b.log', 'SourceReductionResidueCoordinateFinite.lean', 'SourceReductionResidueCoordinateFinite1276a.exit', 'SourceReductionResidueCoordinateFinite1276a.log', 'SourceReductionResidueCoordinateFinite1276b.exit', 'SourceReductionResidueCoordinateFinite1276b.log', 'audit_gamma_one_reduction_1278.ps1', 'audit_gamma_one_reduction_1278b.ps1', 'audit_gamma_one_residue_compatibility_1285.ps1', 'audit_gamma_one_residue_frobenius_1287.ps1', 'audit_gamma_one_residue_places_1291.ps1', 'compile_SourceGammaOneGaussConstants_1272a.ps1', 'compile_SourceGammaOneGaussResidueHom_1270a.ps1', 'compile_SourceGammaOneGaussResidueHom_1270b.ps1', 'compile_SourceGammaOneGaussResidueKernel_1271a.ps1', 'compile_gamma_one_gauss_criterion_1268a.ps1', 'compile_gamma_one_gauss_criterion_1268b.ps1', 'compile_gamma_one_gauss_valuation_1269a.ps1', 'compile_gamma_one_gauss_valuation_1269b.ps1', 'compile_gamma_one_regular_prolongation_1274a.ps1', 'compile_gamma_one_residue_arithmetic_1280a.ps1', 'compile_gamma_one_residue_finite_1277a.ps1', 'compile_gamma_one_residue_finite_1277b.ps1', 'compile_gamma_one_residue_frobenius_1286a.ps1', 'compile_gamma_one_residue_frobenius_1286b.ps1', 'compile_gamma_one_residue_frobenius_1286c.ps1', 'compile_gamma_one_residue_frobenius_1286d.ps1', 'compile_gamma_one_residue_frobenius_places_1290a.ps1', 'compile_gamma_one_residue_hecke_1281a.ps1', 'compile_gamma_one_residue_hecke_1281b.ps1', 'compile_gamma_one_residue_hecke_finite_1282a.ps1', 'compile_gamma_one_residue_image_1273a.ps1', 'compile_gamma_one_residue_image_1273b.ps1', 'compile_gamma_one_residue_j_1275a.ps1', 'compile_gamma_one_residue_place_orders_1289a.ps1', 'compile_gamma_one_residue_places_1288a.ps1', 'compile_gamma_one_residue_separability_1279a.ps1', 'compile_gamma_one_residue_separability_1279b.ps1', 'compile_gamma_one_residue_sequence_1272a.ps1', 'compile_gamma_one_residue_sequence_1272b.ps1', 'compile_residue_coordinate_finite_1276a.ps1', 'compile_residue_coordinate_finite_1276b.ps1', 'consumers1275-focus.log', 'consumers1275.txt', 'consumers1281.txt', 'consumers1283-focus.log', 'consumers1283.txt', 'docs1275.py', 'docs1283.py', 'fetch_curve_candidates_1283c.py', 'fetch_curve_candidates_1283d.py', 'fetch_curve_reuse_1283.py', 'fetch_curve_reuse_1283b.py', 'foundation1275-console.log', 'foundation1283-console.log', 'gamma-one-gauss-route-1268.md', 'gamma-one-reduction-promotion-route-1292.json', 'math1275.txt', 'math1283.txt', 'modules1275.json', 'modules1283.json', 'paper1275-console.log', 'paper1283-console.log', 'prepare_curve_reuse_fetch_1283b.py', 'prepare_gamma_one_reduction_audit_1278.py', 'prepare_gamma_one_reduction_audit_1278b.py', 'prepare_gamma_one_reduction_audit_1278b_generated.py', 'prepare_gamma_one_residue_compatibility_audit_1285.py', 'prepare_gamma_one_residue_frobenius_1286c.py', 'prepare_gamma_one_residue_frobenius_1286d.py', 'prepare_gamma_one_residue_frobenius_audit_1287.py', 'prepare_gamma_one_residue_maps_1270.py', 'prepare_gamma_one_residue_places_audit_1291.py', 'prepare_gamma_one_residue_places_audit_1291_generated.py', 'record1275.py', 'record1283.py', 'record_gamma_one_reduction_1278.py', 'record_gamma_one_reduction_1278b.py', 'record_gamma_one_residue_compatibility_1285.py', 'record_gamma_one_residue_frobenius_1287.py', 'record_gamma_one_residue_places_1291.py', 'register1275.py', 'register1281.py', 'register1283.py', 'register_curve_reuse_1284.py', 'registrations1275.json', 'registrations1283.json', 'remaining1275.txt', 'remaining1283.txt', 'repair_gamma_one_hecke_gauss_1281b.py', 'repair_gamma_one_residue_frobenius_1286b.py', 'repair_residue_separability_1279b.py', 'section1275.txt', 'section1283.txt', 'source-gamma-one-reduction-2-audit-config.json', 'source-gamma-one-reduction-2-reuse-review-20261028.json', 'source-gamma-one-reduction-2-scratch-receipt.json', 'source-gamma-one-reduction-audit-route-1278.json', 'source-gamma-one-reduction-audit-route-1278b.json', 'source-gamma-one-residue-compatibility-1-audit-config.json', 'source-gamma-one-residue-compatibility-1-reuse-review-20261028.json', 'source-gamma-one-residue-compatibility-1-scratch-receipt.json', 'source-gamma-one-residue-compatibility-audit-route-1285.json', 'source-gamma-one-residue-frobenius-1-audit-config.json', 'source-gamma-one-residue-frobenius-1-reuse-review-20261028.json', 'source-gamma-one-residue-frobenius-1-scratch-receipt.json', 'source-gamma-one-residue-frobenius-audit-route-1287.json', 'source-gamma-one-residue-places-1-audit-config.json', 'source-gamma-one-residue-places-1-reuse-review-20261028.json', 'source-gamma-one-residue-places-1-scratch-receipt.json', 'source-gamma-one-residue-places-audit-route-1291.json', 'status1275.txt', 'status1283.txt']]
for folder in ['gamma-one-gauss-criterion-1268a', 'gamma-one-gauss-residue-hom-1270a', 'gamma-one-hecke-gauss-1281a', 'gamma-one-residue-finite-1277a', 'gamma-one-residue-frobenius-1286a', 'gamma-one-residue-frobenius-1286b', 'gamma-one-residue-frobenius-1286c', 'gamma-one-residue-image-1273a', 'gamma-one-residue-separability-1279a', 'residue-coordinate-finite-1276a']:
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
supplemental_review_path=r/archive_rel/'gamma-one-reduction-promotion-route-1292.json'

audit = r / "Extension/Dubon2026/Audit.lean"
at = audit.read_text(encoding="utf-8")
for n in queries:
    assert not re.search(r"``" + re.escape(n) + r"(?=[,\s])", at)
tm, dm = "\n]\n\nprivate def publicConstructions", "\n]\n\nprivate def runAudit"
assert at.count(tm) == at.count(dm) == 1
at = at.replace(tm, "".join("\n  ,``" + n for n in theorems) + tm, 1)
at = at.replace(dm, "".join("\n  ," + chr(96)*2 + n for n in defs) + dm, 1)
research_path = r / "Tools/lean-reuse-audit-20261020.json"
reuse_path = r / "Tools/source-gamma-one-reduction.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt9026"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> original finite Gamma1 arithmetic Hecke realization -> original Picard/Tate Frobenius and inertia -> actual function-field reduction, finite Hecke residue maps and residue-place correspondence.'
discharged = 'Primitive integral Laurent fractions construct the actual coefficient valuation on the original Gamma1 function field. Its literal coefficient reduction has the exact maximal-ideal kernel, actual residue image, constant restriction and nonzero scaling required for a regular prolongation. The original j-coordinate reduces to the literal j Laurent series; its residue coordinate field is finite with degree at most the original degree, and is separable under the explicitly stated perfect-residue-field hypothesis. Original arithmetic decomposition and both original Hecke maps preserve this valuation, with exact coefficient and q-substitution reduction identities. Inertia fixes the actual residue field and its genuine places; both residue Hecke maps are finite. For a decomposition element acting on residue constants by pth power, inverse coefficient action followed by absolute Frobenius is the actual constant-linear q-to-q^p map. It is integral, finite for the original finite-index subgroup containing T, and factors the original residue Hecke beta map through alpha. Its restriction on genuine residue places equals the decomposition permutation, and normalized orders are multiplied by p. These results retain the original field, valuation, Laurent embedding and maps.'
boundary = 'The arithmetic Frobenius action on constants remains an explicit premise. Residue degree upper bounds and finite maps do not establish degree equality or genus preservation. The original Hecke norm reduction identity, compatible original-to-residue place/Picard specialization and prime-to-residue torsion injectivity remain; thus the original geometric Tate Frobenius quadratic and inertia realization remain unproved. Parabolic character realization or a faithful alternative, exceptional primes, coefficient-field realization, original all-weight characteristic-zero association, local/image/regularity, automorphy and literal higher symmetric-power continuation remain. 16/20; DUB-17--20 OPEN; all twenty acceptance tests unchanged.'
status = 'The twenty-module scope passes 91 public axiom queries, 218 exhaustive scratch theorem checks, sixteen linters per module and four declaration-value audits with 96 required dependency checks, with zero diagnostics. Production aggregate, focused audits and sequential foundation/paper verification of the 9,046-module scope are pending.'
route = 'Reuse checks selected native primitive-fraction scaling, reduction-frame independence, the simple pole of j, the perfect-constant separating-coordinate criterion, original decomposition and Hecke field maps, coordinate exchange, discrete-order uniqueness and Laurent Frobenius. Mathlib codRestrict and coe_inclusion avoid normalization of large concrete records without changing proof limits. The fresh pinned AINTLIB and ATLAS review records substantive candidate proofs but does not supply a verified original Gamma1 good-reduction/Picard bridge; the shorter native field route is retained. No general scheme or Jacobian framework, external import or root-pin change is introduced. All promoted mathematical bodies remain identical to their scratch-audited forms after import qualification.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Original Gamma One reduction and residue correspondence (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 9,026-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
corrections = []
count = sum(z['exhaustiveTheorems'] for z in certs)
assert count == 218

docpaths = list(dict.fromkeys(r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]))
for f in docpaths:
    assert "\n\n" in f.read_text(encoding="utf-8")
readmes = [(r.parent / "README.md", "Current Project 83 status ("), (repo / "README.md", "Project 83 has an ")]
for f, prefix in readmes:
    assert sum(line.startswith(prefix) for line in f.read_text(encoding="utf-8").splitlines()) == 1
arch = r / "Dubon Architecture.md"
edge = '  FROBDIAM9026["Exact conditional Frobenius normalization; ambient Galois/Hecke compatibility; native diamond transfer invariance and original full-H1 diamond-one finite character proved. Geometric Frobenius/inertia, parabolic realization, characteristic-zero association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourceGammaOneReductionProductionAudit9046.lean',p/'source-gamma-one-reduction-9046-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production9046.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/frobenius-diamond-20261028-1267'
registered = {row['path'] for row in c['files']}
for priorFile in priorArchive.iterdir():
    rel = priorFile.relative_to(r).as_posix()
    if priorFile.is_file() and rel not in registered:
        c['files'].append({'path': rel, 'role': 'Tools'})

reportSource = p / 'Dubon Original Gamma One Reduction Assessment 2026-10-28.md'
assert sha(reportSource) == '1C6E5BFFB5FF3526264CD59B28C03289DBF97B71B3B6517225B37CBF1D988558'
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
    "productionModules": 9046, "modules": newmods, "queries": queries,
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
arch.write_text(arch.read_text(encoding='utf-8').replace(edge,'  FROBDIAM9026["Exact conditional Frobenius normalization; ambient Galois/Hecke compatibility; native diamond transfer invariance and original full-H1 diamond-one finite character proved (DUB-17/18)"] --> GAMMARED9046\n  GAMMARED9046["Original coefficient valuation and residue field, regular prolongation, finite separating j-coordinate, arithmetic/Hecke residue maps, Frobenius factorization and exact residue-place orders proved. Degree equality, genus, norm identity, original Picard specialization, torsion injectivity and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'),encoding='utf-8')



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Original Gamma One reduction and residue correspondence - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-gamma-one-reduction.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub('  logInfo m!".*"\\n', '  logInfo m!"SOURCE GAMMA ONE REDUCTION AUDIT PASS: {count} theorems including private/generated declarations. Actual original coefficient reduction, finite residue correspondence, conditional Frobenius factorization and residue-place orders. Degree/genus preservation, original Picard specialization and arithmetic realization remain;16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourceGammaOneReductionProductionAudit9046.lean").write_text(out, encoding="utf-8")
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
    target = p / (source.stem + "Production9046.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
(p / "source-gamma-one-reduction-9046-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 9046, "increment": 20, "queries": 91,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
