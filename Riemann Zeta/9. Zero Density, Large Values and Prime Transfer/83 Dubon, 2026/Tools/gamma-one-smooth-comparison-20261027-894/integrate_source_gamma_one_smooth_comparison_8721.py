from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 8695
assert d["appliedSourceGammaOneReciprocityInputs"]["receipt8695"]["exit"] == 0
assert (p / "paper-verification-8695-console.exit").read_text().strip() == "0"
assert (r/'Tools/gamma-one-reciprocity-inputs-20261027-870/canonical-evidence-8695.json').exists()
key = "appliedSourceGammaOneSmoothComparison"
assert key not in d
digests = {'source-gamma-one-untwist-wedge-1-scratch-receipt.json': 'E31FF19C16AA62B73D59CD75CB8DE9910AD2300CE596941B0F9E20E411CC716C', 'source-gamma-one-smooth-partition-1b-scratch-receipt.json': 'DD883E90EBF75A3EC420C700597BC850CF2029CB4BEE5B4EAE2DE11D44FF646D', 'source-gamma-one-petersson-smooth-limit-1-scratch-receipt.json': 'F0CDC72420FF1C5C4BDB12CCF3A202A42D24FEADBD68EFD0CA7060DA729126F9', 'source-modular-parabolic-winding-log-1-scratch-receipt.json': '99DB177F0019C0EBD3D4723848F63371146D544F54D3739A1AF7BB36F66CDECF', 'source-complex-dipole-1-scratch-receipt.json': '6B0A8EC8E086272A388597C7758651D375134515E8F15D6F6C451419B45FD47B'}

for name, digest in digests.items():
    assert sha(p / name) == digest
certs = [json.loads((p / name).read_text(encoding="utf-8")) for name in digests]
mods = [m for z in certs for m in z["modules"]]
queries = [q for z in certs for q in z["queries"]]
theorems = [q for z in certs for q in z["theoremRegistrations"]]
defs = [q for z in certs for q in z["constructionRegistrations"]]
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (26, 26, 220, 186, 34)
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
archive_rel='Tools/gamma-one-smooth-comparison-20261027-894'
evidence=[p/'gamma-one-smooth-comparison-promotion-route-894.json']
evidence += [p/n for n in ['SourceComplexDbarCutoff.lean', 'SourceComplexDipoleAudit1.exit', 'SourceComplexDipoleAudit1.lean', 'SourceComplexDipoleAudit1.log', 'SourceComplexDipoleDependencyAudit1.exit', 'SourceComplexDipoleDependencyAudit1.lean', 'SourceComplexDipoleDependencyAudit1.log', 'SourceComplexDipoleLocalModel.lean', 'SourceComplexDipoleLocalModel891a.exit', 'SourceComplexDipoleLocalModel891a.log', 'SourceComplexDipoleLocalModel891b.exit', 'SourceComplexDipoleLocalModel891b.log', 'SourceComplexDipoleLocalModel891c.exit', 'SourceComplexDipoleLocalModel891c.log', 'SourceComplexDipoleLogDerivative.lean', 'SourceComplexDipoleLogDerivative891b.exit', 'SourceComplexDipoleLogDerivative891b.log', 'SourceComplexDipoleLogDerivative891c.exit', 'SourceComplexDipoleLogDerivative891c.log', 'SourceComplexDipolePairing.lean', 'SourceComplexDipolePairing891b.exit', 'SourceComplexDipolePairing891b.log', 'SourceComplexDipolePairing891c.exit', 'SourceComplexDipolePairing891c.log', 'SourceComplexDipoleScratchOwnership893.exit', 'SourceComplexDipoleScratchOwnership893.lean', 'SourceComplexDipoleScratchOwnership893.log', 'SourceComplexWedgeDisc.lean', 'SourceComplexWedgeDisc872b.exit', 'SourceComplexWedgeDisc872b.log', 'SourceComplexWedgeDisc874a.exit', 'SourceComplexWedgeDisc874a.log', 'SourceComplexWedgeIntegral.lean', 'SourceComplexWedgeIntegral874a.exit', 'SourceComplexWedgeIntegral874a.log', 'SourceComplexWedgeLocalLog.lean', 'SourceComplexWedgeLocalLog872b.exit', 'SourceComplexWedgeLocalLog872b.log', 'SourceComplexWedgeLocalLog872c.exit', 'SourceComplexWedgeLocalLog872c.log', 'SourceComplexWedgeLocalLog874a.exit', 'SourceComplexWedgeLocalLog874a.log', 'SourceComplexWedgeStokes.lean', 'SourceComplexWedgeStokes874a.exit', 'SourceComplexWedgeStokes874a.log', 'SourceComplexWindingLogLift.lean', 'SourceComplexWindingLogLift887a.exit', 'SourceComplexWindingLogLift887a.log', 'SourceGammaOnePeterssonSmoothLimit.lean', 'SourceGammaOnePeterssonSmoothLimit884a.exit', 'SourceGammaOnePeterssonSmoothLimit884a.log', 'SourceGammaOnePeterssonSmoothLimit884b.exit', 'SourceGammaOnePeterssonSmoothLimit884b.log', 'SourceGammaOnePeterssonSmoothLimitAudit1.exit', 'SourceGammaOnePeterssonSmoothLimitAudit1.lean', 'SourceGammaOnePeterssonSmoothLimitAudit1.log', 'SourceGammaOnePeterssonSmoothLimitDependencyAudit1.exit', 'SourceGammaOnePeterssonSmoothLimitDependencyAudit1.lean', 'SourceGammaOnePeterssonSmoothLimitDependencyAudit1.log', 'SourceGammaOnePeterssonSmoothLimitScratchOwnership885.exit', 'SourceGammaOnePeterssonSmoothLimitScratchOwnership885.lean', 'SourceGammaOnePeterssonSmoothLimitScratchOwnership885.log', 'SourceGammaOneSmoothPartition.lean', 'SourceGammaOneSmoothPartition877a.exit', 'SourceGammaOneSmoothPartition877a.log', 'SourceGammaOneSmoothPartition878b.exit', 'SourceGammaOneSmoothPartition878b.log', 'SourceGammaOneSmoothPartitionAudit1b.exit', 'SourceGammaOneSmoothPartitionAudit1b.lean', 'SourceGammaOneSmoothPartitionAudit1b.log', 'SourceGammaOneSmoothPartitionDependencyAudit1b.exit', 'SourceGammaOneSmoothPartitionDependencyAudit1b.lean', 'SourceGammaOneSmoothPartitionDependencyAudit1b.log', 'SourceGammaOneSmoothPartitionScratchOwnership878b.exit', 'SourceGammaOneSmoothPartitionScratchOwnership878b.lean', 'SourceGammaOneSmoothPartitionScratchOwnership878b.log', 'SourceGammaOneUntwistWedgeAudit1.exit', 'SourceGammaOneUntwistWedgeAudit1.lean', 'SourceGammaOneUntwistWedgeAudit1.log', 'SourceGammaOneUntwistWedgeDependencyAudit1.exit', 'SourceGammaOneUntwistWedgeDependencyAudit1.lean', 'SourceGammaOneUntwistWedgeDependencyAudit1.log', 'SourceGammaOneUntwistWedgeIntegral.lean', 'SourceGammaOneUntwistWedgeIntegral874a.exit', 'SourceGammaOneUntwistWedgeIntegral874a.log', 'SourceGammaOneUntwistWedgeScratchOwnership874.exit', 'SourceGammaOneUntwistWedgeScratchOwnership874.lean', 'SourceGammaOneUntwistWedgeScratchOwnership874.log', 'SourceModularInvariantIntegralUnfolding.lean', 'SourceModularInvariantIntegralUnfolding881a.exit', 'SourceModularInvariantIntegralUnfolding881a.log', 'SourceModularInvariantIntegralUnfolding881b.exit', 'SourceModularInvariantIntegralUnfolding881b.log', 'SourceModularParabolicWindingLog.lean', 'SourceModularParabolicWindingLog888a.exit', 'SourceModularParabolicWindingLog888a.log', 'SourceModularParabolicWindingLog888b.exit', 'SourceModularParabolicWindingLog888b.log', 'SourceModularParabolicWindingLogAudit1.exit', 'SourceModularParabolicWindingLogAudit1.lean', 'SourceModularParabolicWindingLogAudit1.log', 'SourceModularParabolicWindingLogDependencyAudit1.exit', 'SourceModularParabolicWindingLogDependencyAudit1.lean', 'SourceModularParabolicWindingLogDependencyAudit1.log', 'SourceModularParabolicWindingLogScratchOwnership890.exit', 'SourceModularParabolicWindingLogScratchOwnership890.lean', 'SourceModularParabolicWindingLogScratchOwnership890.log', 'SourceModularProjectiveFibers.lean', 'SourceModularProjectiveFibers879a.exit', 'SourceModularProjectiveFibers879a.log', 'SourceModularSmoothCosetSum.lean', 'SourceModularSmoothCosetSum876a.exit', 'SourceModularSmoothCosetSum876a.log', 'SourceModularSmoothCosetSum876b.exit', 'SourceModularSmoothCosetSum876b.log', 'SourceModularSmoothCosetSum876c.exit', 'SourceModularSmoothCosetSum876c.log', 'SourceModularSmoothCosetSum876d.exit', 'SourceModularSmoothCosetSum876d.log', 'SourceModularSmoothCosetSum877a.exit', 'SourceModularSmoothCosetSum877a.log', 'SourceModularSmoothCover.lean', 'SourceModularSmoothCover876d.exit', 'SourceModularSmoothCover876d.log', 'SourceModularSmoothCover877a.exit', 'SourceModularSmoothCover877a.log', 'SourceModularSmoothCutoff.lean', 'SourceModularSmoothCutoff875a.exit', 'SourceModularSmoothCutoff875a.log', 'SourceModularSmoothCutoff877a.exit', 'SourceModularSmoothCutoff877a.log', 'SourceModularSmoothGeometry.lean', 'SourceModularSmoothGeometry875a.exit', 'SourceModularSmoothGeometry875a.log', 'SourceModularSmoothGeometry877a.exit', 'SourceModularSmoothGeometry877a.log', 'SourceModularSmoothIntegralLimit.lean', 'SourceModularSmoothIntegralLimit882a.exit', 'SourceModularSmoothIntegralLimit882a.log', 'SourceModularSmoothIntegralLimit882b.exit', 'SourceModularSmoothIntegralLimit882b.log', 'SourceModularSmoothOrbitMass.lean', 'SourceModularSmoothOrbitMass880a.exit', 'SourceModularSmoothOrbitMass880a.log', 'SourceModularSmoothOrbitMass880b.exit', 'SourceModularSmoothOrbitMass880b.log', 'SourceModularSmoothOrbitMass880c.exit', 'SourceModularSmoothOrbitMass880c.log', 'SourceModularSmoothPlaneIntegral.lean', 'SourceModularSmoothPlaneIntegral883a.exit', 'SourceModularSmoothPlaneIntegral883a.log', 'SourceModularSmoothedFundamental.lean', 'SourceModularSmoothedFundamental876e.exit', 'SourceModularSmoothedFundamental876e.log', 'SourceModularSmoothedFundamental877a.exit', 'SourceModularSmoothedFundamental877a.log', 'SourceModularSmoothedFundamental878b.exit', 'SourceModularSmoothedFundamental878b.log', 'SourceModularSmoothedFundamentalSupport.lean', 'SourceModularSmoothedFundamentalSupport876d.exit', 'SourceModularSmoothedFundamentalSupport876d.log', 'SourceModularSmoothedFundamentalSupport876e.exit', 'SourceModularSmoothedFundamentalSupport876e.log', 'SourceModularSmoothedFundamentalSupport877a.exit', 'SourceModularSmoothedFundamentalSupport877a.log', 'SourceModularSmoothedFundamentalSupport878b.exit', 'SourceModularSmoothedFundamentalSupport878b.log', 'SourceModularWindingCharacter.lean', 'SourceModularWindingCharacter887a.exit', 'SourceModularWindingCharacter887a.log', 'SourceModularWindingCuspLimit.lean', 'SourceModularWindingCuspLimit887a.exit', 'SourceModularWindingCuspLimit887a.log', 'SourceUpperHalfPlaneDipole.lean', 'SourceUpperHalfPlaneDipole891c.exit', 'SourceUpperHalfPlaneDipole891c.log', 'SourceUpperHalfPlaneDipole891d.exit', 'SourceUpperHalfPlaneDipole891d.log', 'anthropic-flt-residual-closure-20261020\\Definitions\\Def_ModularCurve_SmoothedFundamental.lean.txt', 'anthropic-flt-residual-closure-20261020\\P2M\\Sol\\S_Complex_integral_logDeriv_wedge_add_finsum_eq_integral_dbarLogDeriv.lean.txt', 'anthropic-flt-residual-closure-20261020\\P2M\\Sol\\S_FLT_Gamma0FundamentalSet_tendsto_integral_mul_smoothedFundamental.lean.txt', 'anthropic-flt-residual-closure-20261020\\P2M\\Sol\\S_ModularCurve_contDiff_and_finsum_smoothedFundamental_eq_one.lean.txt', 'anthropic-flt-residual-closure-20261020\\P2M\\Sol\\S_ModularCurve_exists_exp_eq_of_invariant_ne_zero_isParabolicHom.lean.txt', 'anthropic-flt-residual-closure-20261020\\P2M\\Sol\\S_UpperHalfPlane_exists_localModel_pair_integral_mul_dbarLogDeriv_eq.lean.txt', 'audit887-focused.log', 'complex-dipole-reuse-route-891.json', 'complex-wedge-integral-route-872.json', 'complex-wedge-stokes-route-871.json', 'consumers871.txt', 'consumers877.txt', 'consumers887.txt', 'document877.py', 'download_gamma_one_local_model_construction_889.py', 'download_gamma_one_smooth_local_model_886.py', 'foundation871-console.log', 'foundation877-console.log', 'foundation887-console.log', 'gamma-one-untwist-wedge-route-873.json', 'modular-smooth-partition-route-875.json', 'modular-smooth-partition-route-876.json', 'modules871.json', 'modules877.json', 'modules887.json', 'paper871-console.log', 'paper877-console.log', 'paper887-console.log', 'prepare_complex_dipole_891.py', 'prepare_complex_dipole_audit_893.py', 'prepare_gamma_one_petersson_smooth_limit_audit_885.py', 'prepare_gamma_one_smooth_partition_877.py', 'prepare_gamma_one_smooth_partition_audit_878.py', 'prepare_gamma_one_smooth_partition_audit_878b.py', 'prepare_gamma_one_untwist_wedge_873.py', 'prepare_gamma_one_untwist_wedge_audit_874.py', 'prepare_modular_smooth_partition_875.py', 'prepare_modular_smooth_partition_875b.py', 'prepare_modular_smooth_partition_875c.py', 'prepare_modular_smooth_partition_876.py', 'prepare_parabolic_winding_log_888.py', 'prepare_parabolic_winding_log_audit_890.py', 'prepare_smooth_plane_integral_883.py', 'prepare_wedge_integral_872.py', 'prepare_wedge_stokes_871.py', 'prepare_winding_log_887.py', 'projective-smooth-unfolding-route-879.json', 'record871.py', 'record877.py', 'record887.py', 'record_source_complex_dipole_893.py', 'record_source_gamma_one_petersson_smooth_limit_885.py', 'record_source_gamma_one_smooth_partition_878.py', 'record_source_gamma_one_smooth_partition_878b.py', 'record_source_gamma_one_untwist_wedge_874.py', 'record_source_modular_parabolic_winding_log_890.py', 'register871.py', 'register877.py', 'register887.py', 'registrations871.json', 'registrations877.json', 'registrations887.json', 'section871.txt', 'section877.txt', 'section887.txt', 'smooth-coset-route-adjustment-876d.json', 'smooth-native-unfolding-route-883.json', 'smooth-partition-generator-failure-875a.json', 'smooth-partition-minimal-route-877.json', 'source-complex-dipole-1-audit-config.json', 'source-complex-dipole-1-reuse-review-20261027.json', 'source-complex-dipole-1-scratch-receipt.json', 'source-complex-dipole-audit-route-893.json', 'source-gamma-one-invariant-untwist-1-scratch-receipt.json', 'source-gamma-one-log-derivative-residues-1b-scratch-receipt.json', 'source-gamma-one-petersson-smooth-limit-1-audit-config.json', 'source-gamma-one-petersson-smooth-limit-1-reuse-review-20261027.json', 'source-gamma-one-petersson-smooth-limit-1-scratch-receipt.json', 'source-gamma-one-petersson-smooth-limit-audit-route-885.json', 'source-gamma-one-signed-reciprocity-1-scratch-receipt.json', 'source-gamma-one-smooth-partition-1b-audit-config.json', 'source-gamma-one-smooth-partition-1b-reuse-review-20261027.json', 'source-gamma-one-smooth-partition-1b-scratch-receipt.json', 'source-gamma-one-smooth-partition-audit-route-878.json', 'source-gamma-one-smooth-partition-audit-route-878b.json', 'source-gamma-one-untwist-wedge-1-audit-config.json', 'source-gamma-one-untwist-wedge-1-reuse-review-20261027.json', 'source-gamma-one-untwist-wedge-1-scratch-receipt.json', 'source-gamma-one-untwist-wedge-audit-route-874.json', 'source-modular-parabolic-winding-log-1-audit-config.json', 'source-modular-parabolic-winding-log-1-reuse-review-20261027.json', 'source-modular-parabolic-winding-log-1-scratch-receipt.json', 'source-modular-parabolic-winding-log-audit-route-890.json', 'status871.txt', 'status877.txt', 'status887.txt', 'trim_wedge_route_872c.py', 'trim_wedge_stokes_874a.py', 'wedge-minimal-route-review-872c.json', 'wedge-minimal-route-review-874a.json', 'winding-log-reuse-route-887.json']]
for folder in ['complex-dipole-convex-failed-891c', 'complex-dipole-import-failed-891b', 'complex-dipole-notation-failed-891a', 'gamma-one-local-model-construction-reuse-889', 'gamma-one-petersson-smooth-limit-failed-884a', 'gamma-one-smooth-local-model-reuse-886', 'invariant-unfolding-failed-881a', 'parabolic-winding-log-failed-888a', 'smooth-coset-native-failed-876a', 'smooth-coset-native-failed-876b', 'smooth-coset-native-failed-876c', 'smooth-integral-limit-failed-882a', 'smooth-orbit-mass-failed-880a', 'smooth-orbit-mass-failed-880b', 'smooth-partition-lint-failed-878a', 'smooth-partition-source-before-attribution-877a', 'smooth-support-failed-876d', 'wedge-disc-failed-872a', 'wedge-local-log-failed-872a', 'wedge-local-log-superseded-872b', 'wedge-stokes-superseded-874a']:
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
supplemental_review_path=r/archive_rel/'gamma-one-smooth-comparison-promotion-route-894.json'

audit = r / "Extension/Dubon2026/Audit.lean"
at = audit.read_text(encoding="utf-8")
for n in queries:
    assert not re.search(r"``" + re.escape(n) + r"(?=[,\s])", at)
tm, dm = "\n]\n\nprivate def publicConstructions", "\n]\n\nprivate def runAudit"
assert at.count(tm) == at.count(dm) == 1
at = at.replace(tm, "".join("\n  ,``" + n for n in theorems) + tm, 1)
at = at.replace(dm, "".join("\n  ," + chr(96)*2 + n for n in defs) + dm, 1)
research_path = r / "Tools/lean-reuse-audit-20261020.json"
reuse_path = r / "Tools/source-gamma-one-smooth-comparison.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt8695"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> arithmetic realization of original finite Gamma1 homogeneous-coefficient Hecke characters -> full/parabolic, transpose, diamond, Picard/H1 comparison -> actual differential and period geometry -> Abel-Jacobi principal-divisor converse -> analytic reciprocity.'
discharged = 'The actual original-divisor untwist satisfies the compact C2 wedge/residue identity through proved local integer orders. The literal smooth modular coset partition is constructed with compact support, finite overlap and exact orbit mass. For original Gamma1 weight-two cusp forms, native fundamental-domain unfolding and two-element central fibers prove the source-normalized planar Petersson limit, including integrability and the factor one half on the literal closed coset domain. For an actual nonvanishing invariant C1 function with nonzero finite translated cusp limits, the logarithm, derivative and integral additive character are constructed, and the existing parabolic classification proves squared-trace-four vanishing. Finally an actual compact smooth dipole has orders +1 at s and -1 at b and exact integral pi times the endpoint difference. None of these analytic conclusions is supplied as a certificate.'
boundary = 'The original meromorphic function and its exact divisor orders remain inputs to the untwist consumer. The globally invariant smooth comparison V, exact orbit multiplicities and degree-zero cancellation, filled quotient, winding-period/Petersson assembly, analytic reciprocity and original principal-divisor converse remain. Global integral period/Picard, Hecke/diamond/H1, full/parabolic and transpose comparisons remain. Arithmetic realization of original finite homogeneous-coefficient Gamma1 characters, coefficient-field transport, Frobenius/inertia, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain. Complex semisimplicity, finite characters, Witt coefficients and universal deformation rings do not supply a characteristic-zero lift. 16/20; DUB-17--20 OPEN; all twenty gates unchanged.'
status = 'The twenty-six-module smooth reciprocity ingredient scope passes 220 public axiom queries, 273 exhaustive scratch theorem checks, sixteen linters per module and five declaration-value audits with 258 required dependency checks, with zero diagnostics. Production aggregate, focused audits and sequential foundation/paper verification of the 8,721-module scope are pending.'
route = 'The October 27 reuse search is advanced by locally checked adaptations of pinned Apache-2.0 primary proofs. Existing generic projective domains, finite volume and null boundary replace bespoke finite tilings; native fiber equivalence, unfolding and dominated convergence give the exact central factor. Native proper discontinuity and the Mobius imaginary-part identity construct the source partition. Native exponential covering and uniqueness replace extra lift and local-constancy infrastructure, and the existing parabolic classification replaces an external Period wrapper. The existing wedge/residue theorem and antiholomorphic derivative supply the exact dipole pairing. Unused helpers and external linter suppressions are omitted; root pins and proof limits are unchanged. Promotion changes project import qualification only.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Actual Gamma1 smooth partition, Petersson limit and reciprocity ingredients (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 8,695-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
corrections = []
count = sum(z['exhaustiveTheorems'] for z in certs)
assert count == 273

docpaths = list(dict.fromkeys(r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]))
for f in docpaths:
    assert "\n\n" in f.read_text(encoding="utf-8")
readmes = [(r.parent / "README.md", "Current Project 83 status ("), (repo / "README.md", "Project 83 has an ")]
for f, prefix in readmes:
    assert sum(line.startswith(prefix) for line in f.read_text(encoding="utf-8").splitlines()) == 1
arch = r / "Dubon Architecture.md"
edge = '  GAMMAONERECIPROCITY8695["Actual invariant untwist, signed-to-original periods, degree-zero divisor data and logarithmic residue integral. Modular reciprocity, Abel-Jacobi, Picard/Hecke/H1, all-weight association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourceGammaOneSmoothComparisonProductionAudit8721.lean',p/'source-gamma-one-smooth-comparison-8721-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production8721.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/gamma-one-reciprocity-inputs-20261027-870'
registered = {row['path'] for row in c['files']}
for priorFile in priorArchive.iterdir():
    rel = priorFile.relative_to(r).as_posix()
    if priorFile.is_file() and rel not in registered:
        c['files'].append({'path': rel, 'role': 'Tools'})

reportSource = p / 'Dubon Smooth Reciprocity Reuse Assessment 2026-10-27.md'
assert sha(reportSource) == '2F887255366AE119B38ADF61BC7923446CA69B9A077017FF8D5501408C408A23'
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
    "productionModules": 8721, "modules": newmods, "queries": queries,
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
arch.write_text(arch.read_text(encoding='utf-8').replace(edge,'  GAMMAONERECIPROCITY8695["Actual invariant untwist, signed-to-original periods, degree-zero divisor data and logarithmic residue integral (DUB-17/18)"] --> GAMMAONESMOOTH8721\n  GAMMAONESMOOTH8721["Exact original Gamma1 smooth partition and Petersson limit; wedge, parabolic logarithm and compact dipole proved. Invariant V, winding-period comparison, reciprocity, Abel-Jacobi, Picard/Hecke/H1, all-weight association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'),encoding='utf-8')



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Actual Gamma1 smooth partition, Petersson limit and reciprocity ingredients - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-gamma-one-smooth-comparison.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub('  logInfo m!".*"\\n', '  logInfo m!"SOURCE GAMMA ONE SMOOTH COMPARISON AUDIT PASS: {count} theorems including private/generated declarations. Original Gamma1 smooth partition and Petersson limit, wedge identity, parabolic logarithm and compact dipole are proved. Invariant V, analytic reciprocity and all-weight arithmetic remain; 16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourceGammaOneSmoothComparisonProductionAudit8721.lean").write_text(out, encoding="utf-8")
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
    target = p / (source.stem + "Production8721.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
(p / "source-gamma-one-smooth-comparison-8721-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 8721, "increment": 26, "queries": 220,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
