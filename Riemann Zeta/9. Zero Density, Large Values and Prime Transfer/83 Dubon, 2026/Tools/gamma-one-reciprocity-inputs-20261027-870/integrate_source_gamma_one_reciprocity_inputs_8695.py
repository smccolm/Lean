from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 8674
assert d["appliedSourceGammaOneMultiplierPeriods"]["receipt8674"]["exit"] == 0
assert (p / "paper-verification-8674-console.exit").read_text().strip() == "0"
assert (r/'Tools/gamma-one-multiplier-periods-20261027-847/canonical-evidence-8674.json').exists()
key = "appliedSourceGammaOneReciprocityInputs"
assert key not in d
digests = {'source-gamma-one-invariant-untwist-1-scratch-receipt.json': 'F16ECD3CCDA791603BAD7BEFAB553590188376BCBCA1BB0DCDD0440E84831B20', 'source-gamma-one-divisor-reciprocity-data-1-scratch-receipt.json': '984D203B5BE1D70A272EEE13244BD6DE4C85B798979DD8771617931017BA3CBF', 'source-gamma-one-signed-reciprocity-1-scratch-receipt.json': '2EFDDFE0B99E63D2256BF2EAEBF30B3DAE319D85C1B3589499C480BCE8ECEFB1', 'source-gamma-one-log-derivative-residues-1b-scratch-receipt.json': '978439697AD7EAB0AFEB18AD2DE7C8790FA74DEA3A9773E654EA20CC89D70208'}

for name, digest in digests.items():
    assert sha(p / name) == digest
certs = [json.loads((p / name).read_text(encoding="utf-8")) for name in digests]
mods = [m for z in certs for m in z["modules"]]
queries = [q for z in certs for q in z["queries"]]
theorems = [q for z in certs for q in z["theoremRegistrations"]]
defs = [q for z in certs for q in z["constructionRegistrations"]]
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (21, 21, 108, 98, 10)
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
archive_rel='Tools/gamma-one-reciprocity-inputs-20261027-870'
evidence=[p/'gamma-one-reciprocity-inputs-promotion-route-870.json']
evidence += [p/n for n in ['SourceComplexCauchyPompeiu.exit', 'SourceComplexCauchyPompeiu.lean', 'SourceComplexCauchyPompeiu.log', 'SourceComplexCauchyPompeiu869b.exit', 'SourceComplexCauchyPompeiu869b.log', 'SourceComplexDbarCutoff.exit', 'SourceComplexDbarCutoff.lean', 'SourceComplexDbarCutoff.log', 'SourceComplexDbarCutoff869b.exit', 'SourceComplexDbarCutoff869b.log', 'SourceComplexDbarKernelIntegrability.exit', 'SourceComplexDbarKernelIntegrability.lean', 'SourceComplexDbarKernelIntegrability.log', 'SourceComplexDbarKernelIntegrability869b.exit', 'SourceComplexDbarKernelIntegrability869b.log', 'SourceComplexDbarRadialNormalization.exit', 'SourceComplexDbarRadialNormalization.lean', 'SourceComplexDbarRadialNormalization.log', 'SourceComplexDbarRadialNormalization869b.exit', 'SourceComplexDbarRadialNormalization869b.log', 'SourceComplexHolomorphicStokes.exit', 'SourceComplexHolomorphicStokes.lean', 'SourceComplexHolomorphicStokes.log', 'SourceComplexHolomorphicStokes863b.exit', 'SourceComplexHolomorphicStokes863b.log', 'SourceComplexLogDerivativeResidues.exit', 'SourceComplexLogDerivativeResidues.lean', 'SourceComplexLogDerivativeResidues.log', 'SourceComplexLogDerivativeResidues867b.exit', 'SourceComplexLogDerivativeResidues867b.log', 'SourceComplexLogDerivativeResidues867c.exit', 'SourceComplexLogDerivativeResidues867c.log', 'SourceComplexLogDerivativeResidues869b.exit', 'SourceComplexLogDerivativeResidues869b.log', 'SourceComplexResidueIntegral.exit', 'SourceComplexResidueIntegral.lean', 'SourceComplexResidueIntegral.log', 'SourceComplexResidueIntegral869b.exit', 'SourceComplexResidueIntegral869b.log', 'SourceComplexResidueLocalModels.exit', 'SourceComplexResidueLocalModels.lean', 'SourceComplexResidueLocalModels.log', 'SourceComplexResidueLocalModels869b.exit', 'SourceComplexResidueLocalModels869b.log', 'SourceCuspDerivativeDecay.exit', 'SourceCuspDerivativeDecay.lean', 'SourceCuspDerivativeDecay.log', 'SourceGammaOneDivisorReciprocityData.exit', 'SourceGammaOneDivisorReciprocityData.lean', 'SourceGammaOneDivisorReciprocityData.log', 'SourceGammaOneDivisorReciprocityData859b.exit', 'SourceGammaOneDivisorReciprocityData859b.log', 'SourceGammaOneDivisorReciprocityDataAudit1.exit', 'SourceGammaOneDivisorReciprocityDataAudit1.lean', 'SourceGammaOneDivisorReciprocityDataAudit1.log', 'SourceGammaOneDivisorReciprocityDataDependencyAudit1.exit', 'SourceGammaOneDivisorReciprocityDataDependencyAudit1.lean', 'SourceGammaOneDivisorReciprocityDataDependencyAudit1.log', 'SourceGammaOneDivisorReciprocityDataScratchOwnership860.exit', 'SourceGammaOneDivisorReciprocityDataScratchOwnership860.lean', 'SourceGammaOneDivisorReciprocityDataScratchOwnership860.log', 'SourceGammaOneInvariantUntwist.exit', 'SourceGammaOneInvariantUntwist.lean', 'SourceGammaOneInvariantUntwist.log', 'SourceGammaOneInvariantUntwistAudit1.exit', 'SourceGammaOneInvariantUntwistAudit1.lean', 'SourceGammaOneInvariantUntwistAudit1.log', 'SourceGammaOneInvariantUntwistDependencyAudit1.exit', 'SourceGammaOneInvariantUntwistDependencyAudit1.lean', 'SourceGammaOneInvariantUntwistDependencyAudit1.log', 'SourceGammaOneInvariantUntwistScratchOwnership858.exit', 'SourceGammaOneInvariantUntwistScratchOwnership858.lean', 'SourceGammaOneInvariantUntwistScratchOwnership858.log', 'SourceGammaOneLogDerivativeResidues.exit', 'SourceGammaOneLogDerivativeResidues.lean', 'SourceGammaOneLogDerivativeResidues.log', 'SourceGammaOneLogDerivativeResidues868b.exit', 'SourceGammaOneLogDerivativeResidues868b.log', 'SourceGammaOneLogDerivativeResidues868c.exit', 'SourceGammaOneLogDerivativeResidues868c.log', 'SourceGammaOneLogDerivativeResidues869b.exit', 'SourceGammaOneLogDerivativeResidues869b.log', 'SourceGammaOneLogDerivativeResiduesAudit1b.exit', 'SourceGammaOneLogDerivativeResiduesAudit1b.lean', 'SourceGammaOneLogDerivativeResiduesAudit1b.log', 'SourceGammaOneLogDerivativeResiduesDependencyAudit1.exit', 'SourceGammaOneLogDerivativeResiduesDependencyAudit1.lean', 'SourceGammaOneLogDerivativeResiduesDependencyAudit1.log', 'SourceGammaOneLogDerivativeResiduesScratchOwnership869.exit', 'SourceGammaOneLogDerivativeResiduesScratchOwnership869.lean', 'SourceGammaOneLogDerivativeResiduesScratchOwnership869.log', 'SourceGammaOneSignedReciprocityAudit1.exit', 'SourceGammaOneSignedReciprocityAudit1.lean', 'SourceGammaOneSignedReciprocityAudit1.log', 'SourceGammaOneSignedReciprocityDependencyAudit1.exit', 'SourceGammaOneSignedReciprocityDependencyAudit1.lean', 'SourceGammaOneSignedReciprocityDependencyAudit1.log', 'SourceGammaOneSignedReciprocityScratchOwnership864.exit', 'SourceGammaOneSignedReciprocityScratchOwnership864.lean', 'SourceGammaOneSignedReciprocityScratchOwnership864.log', 'SourceMeromorphicCuspUntwist.exit', 'SourceMeromorphicCuspUntwist.lean', 'SourceMeromorphicCuspUntwist.log', 'SourceMeromorphicCuspUntwist853b.exit', 'SourceMeromorphicCuspUntwist853b.log', 'SourceMeromorphicCuspUntwist853c.exit', 'SourceMeromorphicCuspUntwist853c.log', 'SourceMeromorphicNormalUntwist.exit', 'SourceMeromorphicNormalUntwist.lean', 'SourceMeromorphicNormalUntwist.log', 'SourceMeromorphicNormalUntwist850b.exit', 'SourceMeromorphicNormalUntwist850b.log', 'SourceMeromorphicPeriodUntwist.exit', 'SourceMeromorphicPeriodUntwist.lean', 'SourceMeromorphicPeriodUntwist.log', 'SourceMeromorphicPeriodUntwist851b.exit', 'SourceMeromorphicPeriodUntwist851b.log', 'SourceMeromorphicPeriodUntwist851c.exit', 'SourceMeromorphicPeriodUntwist851c.log', 'SourceMeromorphicPeriodUntwist851d.exit', 'SourceMeromorphicPeriodUntwist851d.log', 'SourceMeromorphicTranslatedGerms.exit', 'SourceMeromorphicTranslatedGerms.lean', 'SourceMeromorphicTranslatedGerms.log', 'SourceMeromorphicTranslatedGerms852b.exit', 'SourceMeromorphicTranslatedGerms852b.log', 'SourceMeromorphicTranslatedGerms852c.exit', 'SourceMeromorphicTranslatedGerms852c.log', 'SourceMeromorphicUntwistDecay.exit', 'SourceMeromorphicUntwistDecay.lean', 'SourceMeromorphicUntwistDecay.log', 'SourceMeromorphicUntwistDecay855b.exit', 'SourceMeromorphicUntwistDecay855b.log', 'SourceMeromorphicUntwistDerivative.exit', 'SourceMeromorphicUntwistDerivative.lean', 'SourceMeromorphicUntwistDerivative.log', 'SourceWeightTwoPeriodUntwist.exit', 'SourceWeightTwoPeriodUntwist.lean', 'SourceWeightTwoPeriodUntwist.log', 'SourceWeightTwoPeriodUntwist849b.exit', 'SourceWeightTwoPeriodUntwist849b.log', 'SourceWeightTwoSignedForms.exit', 'SourceWeightTwoSignedForms.lean', 'SourceWeightTwoSignedForms.log', 'SourceWeightTwoSignedForms861b.exit', 'SourceWeightTwoSignedForms861b.log', 'SourceWeightTwoSignedForms861c.exit', 'SourceWeightTwoSignedForms861c.log', 'SourceWeightTwoSignedReciprocity.exit', 'SourceWeightTwoSignedReciprocity.lean', 'SourceWeightTwoSignedReciprocity.log', 'SourceWeightTwoSignedReciprocity862b.exit', 'SourceWeightTwoSignedReciprocity862b.log', 'SourceWeightTwoSignedReciprocity862c.exit', 'SourceWeightTwoSignedReciprocity862c.log', 'anthropic-flt-residual-closure-20261020\\P2M\\Sol\\S_Complex_integral_inv_sub_mul_dbar_eq_neg_pi_mul.lean.txt', 'anthropic-flt-residual-closure-20261020\\P2M\\Sol\\S_Complex_integral_mul_dbar_eq_neg_pi_mul_finsum_residue.lean.txt', 'anthropic-flt-residual-closure-20261020\\P2M\\Sol\\S_Complex_integral_mul_dbar_eq_zero_of_differentiableOn.lean.txt', 'anthropic-flt-residual-closure-20261020\\P2M\\Sol\\S_Complex_integral_mul_logDeriv_mul_dbar_eq_neg_pi_mul_finsum.lean.txt', 'complex-cauchy-pompeiu-route-865.json', 'complex-holomorphic-stokes-route-863.json', 'complex-log-derivative-residues-route-867.json', 'complex-residue-integral-route-866.json', 'consumers850.txt', 'consumers857.txt', 'download_gamma_one_reciprocity_848.py', 'fix_log_derivative_residue_docs_869b.py', 'fix_log_derivative_residues_867b.py', 'foundation850-console.log', 'foundation857-console.log', 'gamma-one-cusp-derivative-route-854.json', 'gamma-one-cusp-untwist-route-853.json', 'gamma-one-divisor-reciprocity-data-route-859.json', 'gamma-one-invariant-untwist-route-857.json', 'gamma-one-log-derivative-residues-route-868.json', 'gamma-one-meromorphic-untwist-route-851.json', 'gamma-one-normal-untwist-route-850.json', 'gamma-one-period-untwist-route-849.json', 'gamma-one-reciprocity-reuse-848\\S_ModularCurve_exists_invariant_untwist_of_multiplier_eq_exp_periodOf.lean.txt', 'gamma-one-reciprocity-reuse-848\\S_ModularCurve_sum_meromorphicOrderAt_div_card_stabilizer_eq_zero_of_multiplier_eq_exp_periodOf.lean.txt', 'gamma-one-signed-forms-route-861.json', 'gamma-one-signed-reciprocity-route-862.json', 'gamma-one-translated-germs-route-852.json', 'gamma-one-untwist-decay-route-855.json', 'gamma-one-untwist-derivative-route-856.json', 'log-derivative-residues-doc-review-869b.json', 'modules850.json', 'modules857.json', 'paper850-console.log', 'paper857-console.log', 'prepare_cauchy_pompeiu_865.py', 'prepare_cusp_derivative_854.py', 'prepare_cusp_untwist_853.py', 'prepare_divisor_reciprocity_data_859.py', 'prepare_gamma_one_divisor_reciprocity_data_audit_860.py', 'prepare_gamma_one_invariant_untwist_audit_858.py', 'prepare_gamma_one_log_derivative_residues_868.py', 'prepare_gamma_one_log_derivative_residues_audit_869.py', 'prepare_gamma_one_signed_reciprocity_audit_864.py', 'prepare_holomorphic_stokes_863.py', 'prepare_invariant_untwist_857.py', 'prepare_log_derivative_residues_867.py', 'prepare_meromorphic_untwist_851.py', 'prepare_normal_untwist_850.py', 'prepare_period_untwist_849.py', 'prepare_residue_integral_866.py', 'prepare_signed_forms_861.py', 'prepare_signed_reciprocity_862.py', 'prepare_translated_germs_852.py', 'prepare_untwist_decay_855.py', 'prepare_untwist_derivative_856.py', 'record850.py', 'record857.py', 'record_source_gamma_one_divisor_reciprocity_data_860.py', 'record_source_gamma_one_invariant_untwist_858.py', 'record_source_gamma_one_log_derivative_residues_869.py', 'record_source_gamma_one_log_derivative_residues_869b.py', 'record_source_gamma_one_signed_reciprocity_864.py', 'register850.py', 'register857.py', 'registrations850.json', 'registrations857.json', 'section850.txt', 'section857.txt', 'source-gamma-one-divisor-reciprocity-data-1-audit-config.json', 'source-gamma-one-divisor-reciprocity-data-1-reuse-review-20261027.json', 'source-gamma-one-divisor-reciprocity-data-1-scratch-receipt.json', 'source-gamma-one-divisor-reciprocity-data-audit-route-860.json', 'source-gamma-one-invariant-untwist-1-audit-config.json', 'source-gamma-one-invariant-untwist-1-reuse-review-20261027.json', 'source-gamma-one-invariant-untwist-1-scratch-receipt.json', 'source-gamma-one-invariant-untwist-audit-route-858.json', 'source-gamma-one-log-derivative-residues-1b-audit-config.json', 'source-gamma-one-log-derivative-residues-1b-reuse-review-20261027.json', 'source-gamma-one-log-derivative-residues-1b-scratch-receipt.json', 'source-gamma-one-log-derivative-residues-audit-route-869.json', 'source-gamma-one-signed-reciprocity-1-audit-config.json', 'source-gamma-one-signed-reciprocity-1-reuse-review-20261027.json', 'source-gamma-one-signed-reciprocity-1-scratch-receipt.json', 'source-gamma-one-signed-reciprocity-audit-route-864.json', 'status850.txt', 'status857.txt']]
for folder in ['cusp-untwist-failed-853a', 'cusp-untwist-failed-853b', 'divisor-reciprocity-data-failed-859a', 'gamma-one-log-residues-failed-868a', 'gamma-one-log-residues-failed-868b', 'gamma-one-reciprocity-reuse-848', 'holomorphic-stokes-failed-863a', 'log-derivative-residues-failed-867a', 'log-derivative-residues-failed-867b', 'log-derivative-residues-lint-failed-869a', 'meromorphic-untwist-failed-851a', 'meromorphic-untwist-failed-851b', 'meromorphic-untwist-failed-851c', 'normal-untwist-failed-850a', 'period-untwist-failed-849a', 'signed-forms-failed-861a', 'signed-forms-failed-861b', 'signed-reciprocity-failed-862a', 'signed-reciprocity-failed-862b', 'translated-germs-failed-852a', 'translated-germs-failed-852b', 'untwist-decay-failed-855a']:
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
supplemental_review_path=r/archive_rel/'gamma-one-reciprocity-inputs-promotion-route-870.json'

audit = r / "Extension/Dubon2026/Audit.lean"
at = audit.read_text(encoding="utf-8")
for n in queries:
    assert not re.search(r"``" + re.escape(n) + r"(?=[,\s])", at)
tm, dm = "\n]\n\nprivate def publicConstructions", "\n]\n\nprivate def runAudit"
assert at.count(tm) == at.count(dm) == 1
at = at.replace(tm, "".join("\n  ,``" + n for n in theorems) + tm, 1)
at = at.replace(dm, "".join("\n  ," + chr(96)*2 + n for n in defs) + dm, 1)
research_path = r / "Tools/lean-reuse-audit-20261020.json"
reuse_path = r / "Tools/source-gamma-one-reciprocity-inputs.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt8674"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> arithmetic realization of original finite Gamma1 homogeneous-coefficient Hecke characters -> full/parabolic, transpose, diamond, Picard/H1 comparison -> actual differential and period geometry -> Abel-Jacobi principal-divisor converse -> analytic reciprocity.'
discharged = 'For an actual meromorphic function with original Gamma1 divisor orders, unitary multiplier and nonzero translated cusp limits, the specific cusp-form multiplier yields an invariant untwist with exact local integer orders, nonzero cusp limits, derivative decay and an almost-everywhere logarithmic derivative formula. For an actual degree-zero analytic divisor, finite original orbit representatives and the signed stabilizer-weighted zero order sum follow from proved divisor degree and exact ramification. Actual weight-two cusp forms extend across central sign with identical endpoint periods; signed integral periods restrict into the original integer lattice, and actual multiplier and orbit data transport faithfully. Finally, the compact-support logarithmic residue integral consumes the actual original divisor and its ramification-weighted meromorphic orders and the existing actual cusp-form endpoint primitive. The simple-pole kernel normalization, finite residue decomposition and holomorphic integration by parts are proved, not assumed. All nonzero levels and original divisor/coefficient data are retained.'
boundary = 'The actual meromorphic function and its exact original-divisor orders remain inputs; these consumers do not construct that function from the Abel-Jacobi condition. The modular winding-period limit, Petersson comparison, analytic reciprocity and original principal-divisor converse remain. Global integral period/Picard, Hecke/diamond/H1, full/parabolic and transpose comparisons remain. Arithmetic realization of original finite homogeneous-coefficient Gamma1 characters, coefficient-field transport, Frobenius/inertia, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain. Complex semisimplicity, finite characters, Witt coefficients and universal deformation rings do not supply a characteristic-zero lift. 16/20; DUB-17--20 OPEN; all twenty gates unchanged.'
status = 'The twenty-one-module original Gamma1 reciprocity-input scope passes 108 public axiom queries, 156 exhaustive scratch theorem checks, sixteen linters per module and four declaration-value audits with 234 required dependency checks, with zero diagnostics. Production aggregate, focused audits and sequential foundation/paper verification of the 8,695-module scope are pending.'
route = 'The October 27 reuse search is advanced through locally verified adaptations. Native meromorphic normal form and upper-half-plane analytic action replace custom untwist regularization and repeated Mobius calculations; existing endpoint primitives and cusp limits are reused. Existing original divisor degree and exact signed ramification avoid the external general residue-degree proof. Native integer-span induction returns signed periods to the original lattice. Native compact-support integration by parts, radial Haar integration, improper FTC, singular-kernel integrability and logarithmic derivative identities shorten the analytic residue proof. The actual original-divisor consumer connects those foundations to the required chain. The external closure, linter suppressions and unused generalizations are not imported. Promotion changes only project import qualification; audited mathematical bodies, root pins, proof limits and the source contract remain unchanged.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Actual Gamma1 untwist, signed periods and original-divisor residues (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 8,674-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
corrections = []
count = sum(z['exhaustiveTheorems'] for z in certs)
assert count == 156

docpaths = list(dict.fromkeys(r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]))
for f in docpaths:
    assert "\n\n" in f.read_text(encoding="utf-8")
readmes = [(r.parent / "README.md", "Current Project 83 status ("), (repo / "README.md", "Project 83 has an ")]
for f, prefix in readmes:
    assert sum(line.startswith(prefix) for line in f.read_text(encoding="utf-8").splitlines()) == 1
arch = r / "Dubon Architecture.md"
edge = '  GAMMAONEMULTIPLIER8674["Actual closed-chain integral periods and original-divisor meromorphic multiplier realized by cusp periods. Analytic reciprocity, meromorphic construction, Picard/Hecke/H1, all-weight arithmetic association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourceGammaOneReciprocityInputsProductionAudit8695.lean',p/'source-gamma-one-reciprocity-inputs-8695-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production8695.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/gamma-one-multiplier-periods-20261027-847'
registered = {row['path'] for row in c['files']}
for priorFile in priorArchive.iterdir():
    rel = priorFile.relative_to(r).as_posix()
    if priorFile.is_file() and rel not in registered:
        c['files'].append({'path': rel, 'role': 'Tools'})

reportSource = p / 'Dubon Reciprocity Inputs Reuse Assessment 2026-10-27.md'
assert sha(reportSource) == 'D32B896A3B5B86CE8E8EF1885E7FE74F66BD70DD7C7463DF7039DEFDCD2B9339'
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
    "productionModules": 8695, "modules": newmods, "queries": queries,
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
arch.write_text(arch.read_text(encoding='utf-8').replace(edge,'  GAMMAONEMULTIPLIER8674["Actual closed-chain integral periods and original-divisor meromorphic multiplier realized by cusp periods (DUB-17/18)"] --> GAMMAONERECIPROCITY8695\n  GAMMAONERECIPROCITY8695["Actual invariant untwist, signed-to-original periods, degree-zero divisor data and logarithmic residue integral. Modular reciprocity, Abel-Jacobi, Picard/Hecke/H1, all-weight association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'),encoding='utf-8')



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Actual Gamma1 untwist, signed periods and original-divisor residues - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-gamma-one-reciprocity-inputs.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub('  logInfo m!".*"\\n', '  logInfo m!"SOURCE GAMMA ONE RECIPROCITY INPUTS AUDIT PASS: {count} theorems including private/generated declarations. Actual original Gamma1 invariant untwist, signed periods, divisor data and compact-support logarithmic residues are proved. Modular reciprocity and all-weight arithmetic remain; 16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourceGammaOneReciprocityInputsProductionAudit8695.lean").write_text(out, encoding="utf-8")
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
    target = p / (source.stem + "Production8695.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
(p / "source-gamma-one-reciprocity-inputs-8695-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 8695, "increment": 21, "queries": 108,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
