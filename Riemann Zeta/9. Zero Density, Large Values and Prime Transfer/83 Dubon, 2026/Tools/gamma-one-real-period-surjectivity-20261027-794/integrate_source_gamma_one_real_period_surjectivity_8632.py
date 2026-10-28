from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 8599
assert d["appliedSourceGammaOneMeromorphicPrincipalDivisor"]["receipt8599"]["exit"] == 0
assert (p / "paper-verification-8599-console.exit").read_text().strip() == "0"
assert (r/'Tools/gamma-one-meromorphic-principal-divisor-20261027-752/canonical-evidence-8599.json').exists()
key = "appliedSourceGammaOneRealPeriodSurjectivity"
assert key not in d
digests = {'source-gamma-one-real-period-injectivity-1-scratch-receipt.json': '93A114CB4E9D70E5A451CB5383C49DFE670E7E4DB702FF83A3F3CFFA8349715A', 'source-gamma-one-real-parabolic-periods-1-scratch-receipt.json': '4E47B11D4AC61078C31B8FC1BD0CC369081E78CDD95B679EAB4F397534CE9473', 'source-gamma-one-cusp-orbit-invariance-1-scratch-receipt.json': 'FC0A369D24F80013562DC0A6E54DDDF77834C4DBC11BEBE6B849BE4314D19437', 'source-gamma-one-cusp-width-bound-1-scratch-receipt.json': 'B1A53936BB93C534FE13D9A084DA915001D546A3006752ED597B0CB4E81C4010', 'source-gamma-one-exact-cusp-orbits-1-scratch-receipt.json': 'CE5000CF2CC90359306A813F3FD26B58C8773504537EC97EEA7BCD6425811369', 'source-gamma-one-signed-parabolic-1-scratch-receipt.json': '6D3C3243B5FD1B7FCFB20C70D5EDC3F238BB40A9DFD80FB8B070C471320B2EAF', 'source-gamma-one-real-manin-1b-scratch-receipt.json': 'A50C04818EC3CB957D3EB19AF1A1836A6F4D589F8ACC45AE5604FBD8C79C0D00', 'source-gamma-one-real-period-upper-1-scratch-receipt.json': '5FB38D889956491A7EE828B8AE2006CDA1EBE7656F64B6429C62DEFAF1D67909', 'source-gamma-one-canonical-genus-lower-1-scratch-receipt.json': '3B0FDADD90B047D3FC7B9B155158CA07A85726F2F40EE66641DC5245EBB29ED3', 'source-gamma-one-real-period-surjectivity-1-scratch-receipt.json': '3FE2AF35E6932AD06505601DBFAE89029645967837DAAADDE19651BFC850E49F'}

for name, digest in digests.items():
    assert sha(p / name) == digest
certs = [json.loads((p / name).read_text(encoding="utf-8")) for name in digests]
mods = [m for z in certs for m in z["modules"]]
queries = [q for z in certs for q in z["queries"]]
theorems = [q for z in certs for q in z["theoremRegistrations"]]
defs = [q for z in certs for q in z["constructionRegistrations"]]
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (33, 33, 181, 142, 39)
omitted = []
assert not set(mods).intersection(c["productionModules"])
mapping = {m: "Dubon2026." + m for m in c["productionModules"] + mods}
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
        assert f.with_suffix(".exit").read_text().strip() == "0" and f.with_suffix(".log").stat().st_size == 0
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
archive_rel='Tools/gamma-one-real-period-surjectivity-20261027-794'
evidence=[p/'gamma-one-real-period-surjectivity-promotion-route-794.json']
evidence += [p/n for n in ['SourceGammaOneCanonicalCoordinates.exit', 'SourceGammaOneCanonicalCoordinates.lean', 'SourceGammaOneCanonicalCoordinates.log', 'SourceGammaOneCanonicalFiberLower.exit', 'SourceGammaOneCanonicalFiberLower.lean', 'SourceGammaOneCanonicalFiberLower.log', 'SourceGammaOneCanonicalGenusLowerAudit1.exit', 'SourceGammaOneCanonicalGenusLowerAudit1.lean', 'SourceGammaOneCanonicalGenusLowerAudit1.log', 'SourceGammaOneCanonicalGenusLowerDependencyAudit1.exit', 'SourceGammaOneCanonicalGenusLowerDependencyAudit1.lean', 'SourceGammaOneCanonicalGenusLowerDependencyAudit1.log', 'SourceGammaOneCanonicalGenusLowerScratchOwnership789.exit', 'SourceGammaOneCanonicalGenusLowerScratchOwnership789.lean', 'SourceGammaOneCanonicalGenusLowerScratchOwnership789.log', 'SourceGammaOneCentralSignCharacters.exit', 'SourceGammaOneCentralSignCharacters.lean', 'SourceGammaOneCentralSignCharacters.log', 'SourceGammaOneCuspCosetBound.exit', 'SourceGammaOneCuspCosetBound.lean', 'SourceGammaOneCuspCosetBound.log', 'SourceGammaOneCuspCosetPlaces.exit', 'SourceGammaOneCuspCosetPlaces.lean', 'SourceGammaOneCuspCosetPlaces.log', 'SourceGammaOneCuspCyclicOrbit.exit', 'SourceGammaOneCuspCyclicOrbit.lean', 'SourceGammaOneCuspCyclicOrbit.log', 'SourceGammaOneCuspJExactOrder.exit', 'SourceGammaOneCuspJExactOrder.lean', 'SourceGammaOneCuspJExactOrder.log', 'SourceGammaOneCuspOrbitBijection.exit', 'SourceGammaOneCuspOrbitBijection.lean', 'SourceGammaOneCuspOrbitBijection.log', 'SourceGammaOneCuspOrbitInvarianceAudit1.exit', 'SourceGammaOneCuspOrbitInvarianceAudit1.lean', 'SourceGammaOneCuspOrbitInvarianceAudit1.log', 'SourceGammaOneCuspOrbitInvarianceDependencyAudit1.exit', 'SourceGammaOneCuspOrbitInvarianceDependencyAudit1.lean', 'SourceGammaOneCuspOrbitInvarianceDependencyAudit1.log', 'SourceGammaOneCuspOrbitInvarianceScratchOwnership762.exit', 'SourceGammaOneCuspOrbitInvarianceScratchOwnership762.lean', 'SourceGammaOneCuspOrbitInvarianceScratchOwnership762.log', 'SourceGammaOneCuspPlaceLeftInvariance.exit', 'SourceGammaOneCuspPlaceLeftInvariance.lean', 'SourceGammaOneCuspPlaceLeftInvariance.log', 'SourceGammaOneCuspPlaceRightInvariance.exit', 'SourceGammaOneCuspPlaceRightInvariance.lean', 'SourceGammaOneCuspPlaceRightInvariance.log', 'SourceGammaOneCuspPoleDegree.exit', 'SourceGammaOneCuspPoleDegree.lean', 'SourceGammaOneCuspPoleDegree.log', 'SourceGammaOneCuspPositiveWeight.exit', 'SourceGammaOneCuspPositiveWeight.lean', 'SourceGammaOneCuspPositiveWeight.log', 'SourceGammaOneCuspRotationOrder.exit', 'SourceGammaOneCuspRotationOrder.lean', 'SourceGammaOneCuspRotationOrder.log', 'SourceGammaOneCuspTranslationRamification.exit', 'SourceGammaOneCuspTranslationRamification.lean', 'SourceGammaOneCuspTranslationRamification.log', 'SourceGammaOneCuspTranslations.exit', 'SourceGammaOneCuspTranslations.lean', 'SourceGammaOneCuspTranslations.log', 'SourceGammaOneCuspWidthBoundAudit1b.exit', 'SourceGammaOneCuspWidthBoundAudit1b.lean', 'SourceGammaOneCuspWidthBoundAudit1b.log', 'SourceGammaOneCuspWidthBoundDependencyAudit1.exit', 'SourceGammaOneCuspWidthBoundDependencyAudit1.lean', 'SourceGammaOneCuspWidthBoundDependencyAudit1.log', 'SourceGammaOneCuspWidthBoundScratchOwnership767.exit', 'SourceGammaOneCuspWidthBoundScratchOwnership767.lean', 'SourceGammaOneCuspWidthBoundScratchOwnership767.log', 'SourceGammaOneEllipticCosetFiber.exit', 'SourceGammaOneEllipticCosetFiber.lean', 'SourceGammaOneEllipticCosetFiber.log', 'SourceGammaOneEllipticFiberBounds.exit', 'SourceGammaOneEllipticFiberBounds.lean', 'SourceGammaOneEllipticFiberBounds.log', 'SourceGammaOneExactCuspOrbits.exit', 'SourceGammaOneExactCuspOrbits.lean', 'SourceGammaOneExactCuspOrbits.log', 'SourceGammaOneExactCuspOrbitsAudit1.exit', 'SourceGammaOneExactCuspOrbitsAudit1.lean', 'SourceGammaOneExactCuspOrbitsAudit1.log', 'SourceGammaOneExactCuspOrbitsDependencyAudit1.exit', 'SourceGammaOneExactCuspOrbitsDependencyAudit1.lean', 'SourceGammaOneExactCuspOrbitsDependencyAudit1.log', 'SourceGammaOneExactCuspOrbitsScratchOwnership774.exit', 'SourceGammaOneExactCuspOrbitsScratchOwnership774.lean', 'SourceGammaOneExactCuspOrbitsScratchOwnership774.log', 'SourceGammaOneGenusFiberLower.exit', 'SourceGammaOneGenusFiberLower.lean', 'SourceGammaOneGenusFiberLower.log', 'SourceGammaOneInvariantRealPart.exit', 'SourceGammaOneInvariantRealPart.lean', 'SourceGammaOneInvariantRealPart.log', 'SourceGammaOneJDegreeFinsets.exit', 'SourceGammaOneJDegreeFinsets.lean', 'SourceGammaOneJDegreeFinsets.log', 'SourceGammaOneRationalCuspOrbit.exit', 'SourceGammaOneRationalCuspOrbit.lean', 'SourceGammaOneRationalCuspOrbit.log', 'SourceGammaOneRationalCuspPlace.exit', 'SourceGammaOneRationalCuspPlace.lean', 'SourceGammaOneRationalCuspPlace.log', 'SourceGammaOneRationalCyclicCusps.exit', 'SourceGammaOneRationalCyclicCusps.lean', 'SourceGammaOneRationalCyclicCusps.log', 'SourceGammaOneRealCuspPotential.exit', 'SourceGammaOneRealCuspPotential.lean', 'SourceGammaOneRealCuspPotential.log', 'SourceGammaOneRealManinAudit1.exit', 'SourceGammaOneRealManinAudit1.lean', 'SourceGammaOneRealManinAudit1.log', 'SourceGammaOneRealManinCharacter.exit', 'SourceGammaOneRealManinCharacter.lean', 'SourceGammaOneRealManinCharacter.log', 'SourceGammaOneRealManinDependencyAudit1b.exit', 'SourceGammaOneRealManinDependencyAudit1b.lean', 'SourceGammaOneRealManinDependencyAudit1b.log', 'SourceGammaOneRealManinDimension.exit', 'SourceGammaOneRealManinDimension.lean', 'SourceGammaOneRealManinDimension.log', 'SourceGammaOneRealManinScratchOwnership781.exit', 'SourceGammaOneRealManinScratchOwnership781.lean', 'SourceGammaOneRealManinScratchOwnership781.log', 'SourceGammaOneRealParabolicPeriods.exit', 'SourceGammaOneRealParabolicPeriods.lean', 'SourceGammaOneRealParabolicPeriods.log', 'SourceGammaOneRealParabolicPeriodsAudit1.exit', 'SourceGammaOneRealParabolicPeriodsAudit1.lean', 'SourceGammaOneRealParabolicPeriodsAudit1.log', 'SourceGammaOneRealParabolicPeriodsDependencyAudit1.exit', 'SourceGammaOneRealParabolicPeriodsDependencyAudit1.lean', 'SourceGammaOneRealParabolicPeriodsDependencyAudit1.log', 'SourceGammaOneRealParabolicPeriodsScratchOwnership758.exit', 'SourceGammaOneRealParabolicPeriodsScratchOwnership758.lean', 'SourceGammaOneRealParabolicPeriodsScratchOwnership758.log', 'SourceGammaOneRealPeriodDimensionUpper.exit', 'SourceGammaOneRealPeriodDimensionUpper.lean', 'SourceGammaOneRealPeriodDimensionUpper.log', 'SourceGammaOneRealPeriodInjectivity.exit', 'SourceGammaOneRealPeriodInjectivity.lean', 'SourceGammaOneRealPeriodInjectivity.log', 'SourceGammaOneRealPeriodInjectivityAudit1.exit', 'SourceGammaOneRealPeriodInjectivityAudit1.lean', 'SourceGammaOneRealPeriodInjectivityAudit1.log', 'SourceGammaOneRealPeriodInjectivityDependencyAudit1.exit', 'SourceGammaOneRealPeriodInjectivityDependencyAudit1.lean', 'SourceGammaOneRealPeriodInjectivityDependencyAudit1.log', 'SourceGammaOneRealPeriodInjectivityScratchOwnership756.exit', 'SourceGammaOneRealPeriodInjectivityScratchOwnership756.lean', 'SourceGammaOneRealPeriodInjectivityScratchOwnership756.log', 'SourceGammaOneRealPeriodMap.exit', 'SourceGammaOneRealPeriodMap.lean', 'SourceGammaOneRealPeriodMap.log', 'SourceGammaOneRealPeriodSurjectivity.exit', 'SourceGammaOneRealPeriodSurjectivity.lean', 'SourceGammaOneRealPeriodSurjectivity.log', 'SourceGammaOneRealPeriodSurjectivityAudit1.exit', 'SourceGammaOneRealPeriodSurjectivityAudit1.lean', 'SourceGammaOneRealPeriodSurjectivityAudit1.log', 'SourceGammaOneRealPeriodSurjectivityDependencyAudit1.exit', 'SourceGammaOneRealPeriodSurjectivityDependencyAudit1.lean', 'SourceGammaOneRealPeriodSurjectivityDependencyAudit1.log', 'SourceGammaOneRealPeriodSurjectivityScratchOwnership793.exit', 'SourceGammaOneRealPeriodSurjectivityScratchOwnership793.lean', 'SourceGammaOneRealPeriodSurjectivityScratchOwnership793.log', 'SourceGammaOneRealPeriodUpperAudit1.exit', 'SourceGammaOneRealPeriodUpperAudit1.lean', 'SourceGammaOneRealPeriodUpperAudit1.log', 'SourceGammaOneRealPeriodUpperDependencyAudit1.exit', 'SourceGammaOneRealPeriodUpperDependencyAudit1.lean', 'SourceGammaOneRealPeriodUpperDependencyAudit1.log', 'SourceGammaOneRealPeriodUpperScratchOwnership784.exit', 'SourceGammaOneRealPeriodUpperScratchOwnership784.lean', 'SourceGammaOneRealPeriodUpperScratchOwnership784.log', 'SourceGammaOneSignedParabolicAudit1.exit', 'SourceGammaOneSignedParabolicAudit1.lean', 'SourceGammaOneSignedParabolicAudit1.log', 'SourceGammaOneSignedParabolicCharacters.exit', 'SourceGammaOneSignedParabolicCharacters.lean', 'SourceGammaOneSignedParabolicCharacters.log', 'SourceGammaOneSignedParabolicDependencyAudit1.exit', 'SourceGammaOneSignedParabolicDependencyAudit1.lean', 'SourceGammaOneSignedParabolicDependencyAudit1.log', 'SourceGammaOneSignedParabolicScratchOwnership777.exit', 'SourceGammaOneSignedParabolicScratchOwnership777.lean', 'SourceGammaOneSignedParabolicScratchOwnership777.log', 'download_gamma_one_period_core_795.py', 'download_gamma_one_period_core_795b.py', 'gamma-one-canonical-genus-lower-audit-route-789.json', 'gamma-one-cusp-orbit-invariance-audit-route-762.json', 'gamma-one-cusp-orbit-preparer-failure-762a.json', 'gamma-one-cusp-period-dimension-route-759.json', 'gamma-one-cusp-width-bound-audit-route-767.json', 'gamma-one-cusp-width-bound-route-766.json', 'gamma-one-exact-cusp-orbits-audit-route-774.json', 'gamma-one-genus-lower-route-785.json', 'gamma-one-real-manin-audit-route-781.json', 'gamma-one-real-manin-preflight-781b.json', 'gamma-one-real-manin-route-775.json', 'gamma-one-real-parabolic-periods-audit-route-758.json', 'gamma-one-real-period-injectivity-audit-route-756.json', 'gamma-one-real-period-injectivity-route-756.json', 'gamma-one-real-period-surjectivity-audit-route-793.json', 'gamma-one-real-period-upper-audit-route-784.json', 'gamma-one-signed-parabolic-audit-route-777.json', 'prepare_gamma_one_canonical_genus_lower_audit_789.py', 'prepare_gamma_one_cusp_orbit_invariance_audit_762b.py', 'prepare_gamma_one_cusp_width_bound_audit_767.py', 'prepare_gamma_one_exact_cusp_orbits_audit_774.py', 'prepare_gamma_one_real_manin_audit_781.py', 'prepare_gamma_one_real_parabolic_periods_audit_758.py', 'prepare_gamma_one_real_period_injectivity_audit_756.py', 'prepare_gamma_one_real_period_surjectivity_audit_793.py', 'prepare_gamma_one_real_period_upper_audit_784.py', 'prepare_gamma_one_signed_parabolic_audit_777.py', 'record_gamma_one_canonical_genus_lower_789.py', 'record_gamma_one_cusp_orbit_invariance_762.py', 'record_gamma_one_cusp_width_bound_767.py', 'record_gamma_one_cusp_width_bound_767b.py', 'record_gamma_one_exact_cusp_orbits_774.py', 'record_gamma_one_real_manin_781.py', 'record_gamma_one_real_manin_781b.py', 'record_gamma_one_real_parabolic_periods_758.py', 'record_gamma_one_real_period_injectivity_756.py', 'record_gamma_one_real_period_surjectivity_793.py', 'record_gamma_one_real_period_upper_784.py', 'record_gamma_one_signed_parabolic_777.py', 'source-gamma-one-canonical-genus-lower-1-audit-config.json', 'source-gamma-one-canonical-genus-lower-1-reuse-review-20261027.json', 'source-gamma-one-canonical-genus-lower-1-scratch-receipt.json', 'source-gamma-one-cusp-orbit-invariance-1-audit-config.json', 'source-gamma-one-cusp-orbit-invariance-1-reuse-review-20261027.json', 'source-gamma-one-cusp-orbit-invariance-1-scratch-receipt.json', 'source-gamma-one-cusp-width-bound-1-audit-config.json', 'source-gamma-one-cusp-width-bound-1-reuse-review-20261027.json', 'source-gamma-one-cusp-width-bound-1-scratch-receipt.json', 'source-gamma-one-exact-cusp-orbits-1-audit-config.json', 'source-gamma-one-exact-cusp-orbits-1-reuse-review-20261027.json', 'source-gamma-one-exact-cusp-orbits-1-scratch-receipt.json', 'source-gamma-one-real-manin-1b-audit-config.json', 'source-gamma-one-real-manin-1b-reuse-review-20261027.json', 'source-gamma-one-real-manin-1b-scratch-receipt.json', 'source-gamma-one-real-parabolic-periods-1-audit-config.json', 'source-gamma-one-real-parabolic-periods-1-reuse-review-20261027.json', 'source-gamma-one-real-parabolic-periods-1-scratch-receipt.json', 'source-gamma-one-real-period-injectivity-1-audit-config.json', 'source-gamma-one-real-period-injectivity-1-reuse-review-20261027.json', 'source-gamma-one-real-period-injectivity-1-scratch-receipt.json', 'source-gamma-one-real-period-surjectivity-1-audit-config.json', 'source-gamma-one-real-period-surjectivity-1-reuse-review-20261027.json', 'source-gamma-one-real-period-surjectivity-1-scratch-receipt.json', 'source-gamma-one-real-period-upper-1-audit-config.json', 'source-gamma-one-real-period-upper-1-reuse-review-20261027.json', 'source-gamma-one-real-period-upper-1-scratch-receipt.json', 'source-gamma-one-signed-parabolic-1-audit-config.json', 'source-gamma-one-signed-parabolic-1-reuse-review-20261027.json', 'source-gamma-one-signed-parabolic-1-scratch-receipt.json']]
for folder in ['gamma-one-canonical-coordinates-failed-785a', 'gamma-one-canonical-fiber-lower-failed-787a', 'gamma-one-central-sign-characters-failed-775a', 'gamma-one-cusp-j-exact-order-failed-764a', 'gamma-one-cusp-orbit-bijection-failed-772a', 'gamma-one-cusp-place-left-failed-759a', 'gamma-one-cusp-place-right-failed-761a', 'gamma-one-cusp-place-right-failed-761b', 'gamma-one-cusp-place-right-failed-761c', 'gamma-one-cusp-pole-degree-failed-770a', 'gamma-one-cusp-width-bound-failed-767a', 'gamma-one-elliptic-coset-fiber-failed-790a', 'gamma-one-period-core-reuse-795', 'gamma-one-period-core-reuse-795b', 'gamma-one-rational-cusp-orbit-failed-763a', 'gamma-one-rational-cyclic-cusps-failed-782a', 'gamma-one-real-manin-dimension-failed-780a', 'gamma-one-real-manin-dimension-failed-780b', 'gamma-one-real-period-injectivity-failed-756a', 'gamma-one-real-period-map-failed-757a', 'gamma-one-real-period-surjectivity-failed-792a', 'gamma-one-real-period-surjectivity-failed-792b', 'gamma-one-real-period-surjectivity-failed-792c', 'gamma-one-signed-parabolic-characters-failed-776a']:
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
supplemental_review_path=r/archive_rel/'gamma-one-real-period-surjectivity-promotion-route-794.json'

audit = r / "Extension/Dubon2026/Audit.lean"
at = audit.read_text(encoding="utf-8")
for n in queries:
    assert not re.search(r"``" + re.escape(n) + r"(?=[,\s])", at)
tm, dm = "\n]\n\nprivate def publicConstructions", "\n]\n\nprivate def runAudit"
assert at.count(tm) == at.count(dm) == 1
at = at.replace(tm, "".join("\n  ,``" + n for n in theorems) + tm, 1)
at = at.replace(dm, "".join("\n  ," + chr(96)*2 + n for n in defs) + dm, 1)
research_path = r / "Tools/lean-reuse-audit-20261020.json"
reuse_path = r / "Tools/source-gamma-one-real-period-surjectivity.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt8599"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> arithmetic realization of original finite Gamma1 homogeneous-coefficient Hecke characters -> full/parabolic, transpose, diamond, Picard/H1 comparison -> actual differential and period geometry -> Abel-Jacobi principal-divisor converse.'
discharged = 'Every real parabolic character of the ORIGINAL Gamma1 subgroup is realized by the real periods of an actual weight-two cusp form, at every nonzero level. The actual period map is a real-linear equivalence. Native fundamental-tile maximum principles prove injectivity; cusp limits prove parabolicity. Actual rational cusp and cyclic signed-coset orbits are bijective with all original j-pole places, with exact pole orders. The central-sign character extension is injective and preserves parabolicity. Reusing the generic Manin relation bound, finite-coordinate canonical degree and literal Fourier differential/cusp equivalence proves matching dimension bounds. Actual elliptic fiber surjections suffice for the required genus lower bound. No real-period, dimension, genus, cusp-count, elliptic-cardinality or character-extension hypothesis remains.'
boundary = 'Reciprocity and construction of meromorphic functions from the Abel-Jacobi period condition remain. Actual global integral periods and Hecke/diamond/Picard/H1, full/parabolic and transpose comparisons remain. Arithmetic realization of original finite homogeneous-coefficient Gamma1 characters, coefficient-field transport, Frobenius/inertia, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain. Complex semisimplicity, finite characters, Witt coefficients and universal deformation rings do not supply a characteristic-zero lift. 16/20; DUB-17--20 OPEN; all twenty gates unchanged.'
status = 'The thirty-three-module original Gamma1 real-period realization passes 181 public axiom queries, 291 exhaustive scratch theorem checks, sixteen linters per module and ten declaration-value audits covering 254 required dependencies, with zero diagnostics. Production aggregate, focused audits and sequential foundation/paper verification of the 8,632-module scope are pending.'
route = 'The October 27 reuse refresh and pinned primary review are applied to the direct original Gamma1 route. Existing local period primitives, finite H1, signed subgroup geometry, exact j degree, generic Manin relations, canonical degree and literal Fourier comparison are reused. The required lower bound avoids an unnecessary exact genus formula, elliptic fiber injectivity proof and independent arithmetic cusp enumeration. Only imports are qualified on promotion; audited statements and proof bodies remain identical. Failed attempts and further primary reciprocity snapshots are preserved. External import closures are not locally built. Root pins, proof limits, source fidelity and the full all-weight contract are unchanged.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Actual Gamma1 real-period realization (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 8,599-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
corrections = []
count = sum(z['exhaustiveTheorems'] for z in certs)
assert count == 291

docpaths = list(dict.fromkeys(r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]))
for f in docpaths:
    assert "\n\n" in f.read_text(encoding="utf-8")
readmes = [(r.parent / "README.md", "Current Project 83 status ("), (repo / "README.md", "Project 83 has an ")]
for f, prefix in readmes:
    assert sum(line.startswith(prefix) for line in f.read_text(encoding="utf-8").splitlines()) == 1
arch = r / "Dubon Architecture.md"
edge = '  GAMMAONEPRINCIPAL8599["Original-field meromorphic principal-divisor conversion and every cusp order proved. Function construction from periods, Hecke/diamond/Picard/H1, all-weight arithmetic association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourceGammaOneRealPeriodSurjectivityProductionAudit8632.lean',p/'source-gamma-one-real-period-surjectivity-8632-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production8632.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/gamma-one-meromorphic-principal-divisor-20261027-752'
registered = {row['path'] for row in c['files']}
for priorFile in priorArchive.iterdir():
    rel = priorFile.relative_to(r).as_posix()
    if priorFile.is_file() and rel not in registered:
        c['files'].append({'path': rel, 'role': 'Tools'})

reportSource = p / 'Dubon Real Period Reuse Assessment 2026-10-27.md'
assert sha(reportSource) == '6B480D104F88BC3D76E32F0EFF4D0664EA29A9A6F6594A2F0174B57E78663B6D'
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
    "productionModules": 8632, "modules": newmods, "queries": queries,
    "theoremRegistrations": theorems, "constructionRegistrations": defs,
    "sourceHashes": {mapping[t.stem]: sha(t) for t, _ in pending}, "scratchCertificates": certs,
    "exactDependency": dependency, "assumptionsDischarged": discharged, "stillOpen": boundary,
    "status": status, "rootPinsChanged": False, "proofLimitsChanged": False,
    "promotionChanges": 'Only scratch imports are qualified. All audited statements, proof bodies and comments remain identical. The original Gamma1 field, every nonzero level, actual real period map, exact cusp places and genuine parabolic characters are retained.',
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
arch.write_text(arch.read_text(encoding='utf-8').replace(edge,'  GAMMAONEPRINCIPAL8599["Original-field meromorphic principal-divisor conversion with every cusp order (DUB-17/18)"] --> GAMMAONEREALPERIOD8632\n  GAMMAONEREALPERIOD8632["Every original Gamma1 real parabolic character realized by actual weight-two cusp periods. Reciprocity, Picard/Hecke/diamond/H1, all-weight arithmetic association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'),encoding='utf-8')



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Actual Gamma1 real-period realization - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-gamma-one-real-period-surjectivity.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub('  logInfo m!".*"\\n', '  logInfo m!"SOURCE GAMMA ONE REAL PERIOD SURJECTIVITY AUDIT PASS: {count} theorems including private/generated declarations. Every original real Gamma1 parabolic character is realized by an actual weight-two cusp form. Reciprocity and original arithmetic comparison remain; 16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourceGammaOneRealPeriodSurjectivityProductionAudit8632.lean").write_text(out, encoding="utf-8")
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
    target = p / (source.stem + "Production8632.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
(p / "source-gamma-one-real-period-surjectivity-8632-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 8632, "increment": 33, "queries": 181,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
