from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 8632
assert d["appliedSourceGammaOneRealPeriodSurjectivity"]["receipt8632"]["exit"] == 0
assert (p / "paper-verification-8632-console.exit").read_text().strip() == "0"
assert (r/'Tools/gamma-one-real-period-surjectivity-20261027-794/canonical-evidence-8632.json').exists()
key = "appliedSourceGammaOneMultiplierPeriods"
assert key not in d
digests = {'source-gamma-one-closed-chain-periods-1-scratch-receipt.json': 'E2697646D6D1953384FA5C10AA8743EA73BDED3A4AD1820B660B0651AE1AF67B', 'source-modular-free-product-1-scratch-receipt.json': '289323F43C4D06438774F2B981891A52B95AE22056F49A5F3D6A3F43504C1A39', 'source-cusp-correction-1-scratch-receipt.json': 'E84B9DC7BBB941D303A9AE19BB7E415C7E3C32E483689901BDC7C16E1A16446B', 'source-integral-parabolic-character-lift-1-scratch-receipt.json': '3D1D02285ABF36559365D7B6C0F49A47E8513F90ED49D004A1A62C0BAE18A40A', 'source-gamma-one-unitary-character-periods-1c-scratch-receipt.json': '3F98EF6171E950E6A807E30137A8C53C883FE222B613C0CE102F487537B00E16', 'source-gamma-one-meromorphic-multiplier-periods-1-scratch-receipt.json': 'F777D01F63B92C278B10B37A3B90F6D1BCA4F6BFE2F3EA17C98F8D757D5D3E0D'}

for name, digest in digests.items():
    assert sha(p / name) == digest
certs = [json.loads((p / name).read_text(encoding="utf-8")) for name in digests]
mods = [m for z in certs for m in z["modules"]]
queries = [q for z in certs for q in z["queries"]]
theorems = [q for z in certs for q in z["theoremRegistrations"]]
defs = [q for z in certs for q in z["constructionRegistrations"]]
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (42, 42, 273, 207, 66)
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
archive_rel='Tools/gamma-one-multiplier-periods-20261027-847'
evidence=[p/'gamma-one-multiplier-periods-promotion-route-847.json']
evidence += [p/n for n in ['SourceCuspCorrectionAudit1.exit', 'SourceCuspCorrectionAudit1.lean', 'SourceCuspCorrectionAudit1.log', 'SourceCuspCorrectionCosetChains.exit', 'SourceCuspCorrectionCosetChains.lean', 'SourceCuspCorrectionCosetChains.log', 'SourceCuspCorrectionCyclicCosets.exit', 'SourceCuspCorrectionCyclicCosets.lean', 'SourceCuspCorrectionCyclicCosets.log', 'SourceCuspCorrectionDependencyAudit1.exit', 'SourceCuspCorrectionDependencyAudit1.lean', 'SourceCuspCorrectionDependencyAudit1.log', 'SourceCuspCorrectionEdgeChains.exit', 'SourceCuspCorrectionEdgeChains.lean', 'SourceCuspCorrectionEdgeChains.log', 'SourceCuspCorrectionEdgeCharacters.exit', 'SourceCuspCorrectionEdgeCharacters.lean', 'SourceCuspCorrectionEdgeCharacters.log', 'SourceCuspCorrectionGenerators.exit', 'SourceCuspCorrectionGenerators.lean', 'SourceCuspCorrectionGenerators.log', 'SourceCuspCorrectionRealization.exit', 'SourceCuspCorrectionRealization.lean', 'SourceCuspCorrectionRealization.log', 'SourceCuspCorrectionScratchOwnership817.exit', 'SourceCuspCorrectionScratchOwnership817.lean', 'SourceCuspCorrectionScratchOwnership817.log', 'SourceGammaOneClosedChainIntegral.exit', 'SourceGammaOneClosedChainIntegral.lean', 'SourceGammaOneClosedChainIntegral.log', 'SourceGammaOneClosedChainPeriodsAudit1.exit', 'SourceGammaOneClosedChainPeriodsAudit1.lean', 'SourceGammaOneClosedChainPeriodsAudit1.log', 'SourceGammaOneClosedChainPeriodsDependencyAudit1.exit', 'SourceGammaOneClosedChainPeriodsDependencyAudit1.lean', 'SourceGammaOneClosedChainPeriodsDependencyAudit1.log', 'SourceGammaOneClosedChainPeriodsScratchOwnership804.exit', 'SourceGammaOneClosedChainPeriodsScratchOwnership804.lean', 'SourceGammaOneClosedChainPeriodsScratchOwnership804.log', 'SourceGammaOneIntegralParabolicLift.exit', 'SourceGammaOneIntegralParabolicLift.lean', 'SourceGammaOneIntegralParabolicLift.log', 'SourceGammaOneMeromorphicMultiplierElliptic.exit', 'SourceGammaOneMeromorphicMultiplierElliptic.lean', 'SourceGammaOneMeromorphicMultiplierElliptic.log', 'SourceGammaOneMeromorphicMultiplierPeriods.exit', 'SourceGammaOneMeromorphicMultiplierPeriods.lean', 'SourceGammaOneMeromorphicMultiplierPeriods.log', 'SourceGammaOneMeromorphicMultiplierPeriodsAudit1.exit', 'SourceGammaOneMeromorphicMultiplierPeriodsAudit1.lean', 'SourceGammaOneMeromorphicMultiplierPeriodsAudit1.log', 'SourceGammaOneMeromorphicMultiplierPeriodsDependencyAudit1.exit', 'SourceGammaOneMeromorphicMultiplierPeriodsDependencyAudit1.lean', 'SourceGammaOneMeromorphicMultiplierPeriodsDependencyAudit1.log', 'SourceGammaOneMeromorphicMultiplierPeriodsScratchOwnership846.exit', 'SourceGammaOneMeromorphicMultiplierPeriodsScratchOwnership846.lean', 'SourceGammaOneMeromorphicMultiplierPeriodsScratchOwnership846.log', 'SourceGammaOneUnitaryCharacterPeriods.exit', 'SourceGammaOneUnitaryCharacterPeriods.lean', 'SourceGammaOneUnitaryCharacterPeriods.log', 'SourceGammaOneUnitaryCharacterPeriodsAudit1.exit', 'SourceGammaOneUnitaryCharacterPeriodsAudit1.lean', 'SourceGammaOneUnitaryCharacterPeriodsAudit1.log', 'SourceGammaOneUnitaryCharacterPeriodsAudit1b.exit', 'SourceGammaOneUnitaryCharacterPeriodsAudit1b.lean', 'SourceGammaOneUnitaryCharacterPeriodsAudit1b.log', 'SourceGammaOneUnitaryCharacterPeriodsAudit1c.exit', 'SourceGammaOneUnitaryCharacterPeriodsAudit1c.lean', 'SourceGammaOneUnitaryCharacterPeriodsAudit1c.log', 'SourceGammaOneUnitaryCharacterPeriodsDependencyAudit1.exit', 'SourceGammaOneUnitaryCharacterPeriodsDependencyAudit1.lean', 'SourceGammaOneUnitaryCharacterPeriodsDependencyAudit1.log', 'SourceGammaOneUnitaryCharacterPeriodsScratchOwnership840.exit', 'SourceGammaOneUnitaryCharacterPeriodsScratchOwnership840.lean', 'SourceGammaOneUnitaryCharacterPeriodsScratchOwnership840.log', 'SourceIntegralCharacterCorrection.exit', 'SourceIntegralCharacterCorrection.lean', 'SourceIntegralCharacterCorrection.log', 'SourceIntegralCharacterCrossed.exit', 'SourceIntegralCharacterCrossed.lean', 'SourceIntegralCharacterCrossed.log', 'SourceIntegralCharacterCuspConjugacy.exit', 'SourceIntegralCharacterCuspConjugacy.lean', 'SourceIntegralCharacterCuspConjugacy.log', 'SourceIntegralCharacterCuspSum.exit', 'SourceIntegralCharacterCuspSum.lean', 'SourceIntegralCharacterCuspSum.log', 'SourceIntegralCharacterFreeProduct.exit', 'SourceIntegralCharacterFreeProduct.lean', 'SourceIntegralCharacterFreeProduct.log', 'SourceIntegralCharacterInitialLift.exit', 'SourceIntegralCharacterInitialLift.lean', 'SourceIntegralCharacterInitialLift.log', 'SourceIntegralCharacterModularBridge.exit', 'SourceIntegralCharacterModularBridge.lean', 'SourceIntegralCharacterModularBridge.log', 'SourceIntegralCharacterModularFacts.exit', 'SourceIntegralCharacterModularFacts.lean', 'SourceIntegralCharacterModularFacts.log', 'SourceIntegralCharacterPotential.exit', 'SourceIntegralCharacterPotential.lean', 'SourceIntegralCharacterPotential.log', 'SourceIntegralCharacterShapiro.exit', 'SourceIntegralCharacterShapiro.lean', 'SourceIntegralCharacterShapiro.log', 'SourceIntegralParabolicCharacterLift.exit', 'SourceIntegralParabolicCharacterLift.lean', 'SourceIntegralParabolicCharacterLift.log', 'SourceIntegralParabolicCharacterLiftAudit1.exit', 'SourceIntegralParabolicCharacterLiftAudit1.lean', 'SourceIntegralParabolicCharacterLiftAudit1.log', 'SourceIntegralParabolicCharacterLiftDependencyAudit1.exit', 'SourceIntegralParabolicCharacterLiftDependencyAudit1.lean', 'SourceIntegralParabolicCharacterLiftDependencyAudit1.log', 'SourceIntegralParabolicCharacterLiftScratchOwnership830.exit', 'SourceIntegralParabolicCharacterLiftScratchOwnership830.lean', 'SourceIntegralParabolicCharacterLiftScratchOwnership830.log', 'SourceMeromorphicMultiplierGerm.exit', 'SourceMeromorphicMultiplierGerm.lean', 'SourceMeromorphicMultiplierGerm.log', 'SourceMeromorphicMultiplierParabolic.exit', 'SourceMeromorphicMultiplierParabolic.lean', 'SourceMeromorphicMultiplierParabolic.log', 'SourceModularEllipticFixedPoint.exit', 'SourceModularEllipticFixedPoint.lean', 'SourceModularEllipticFixedPoint.log', 'SourceModularFreeProduct.exit', 'SourceModularFreeProduct.lean', 'SourceModularFreeProduct.log', 'SourceModularFreeProductAudit1.exit', 'SourceModularFreeProductAudit1.lean', 'SourceModularFreeProductAudit1.log', 'SourceModularFreeProductAudit1b.exit', 'SourceModularFreeProductAudit1b.lean', 'SourceModularFreeProductAudit1b.log', 'SourceModularFreeProductDependencyAudit1.exit', 'SourceModularFreeProductDependencyAudit1.lean', 'SourceModularFreeProductDependencyAudit1.log', 'SourceModularFreeProductInjection.exit', 'SourceModularFreeProductInjection.lean', 'SourceModularFreeProductInjection.log', 'SourceModularFreeProductScratchOwnership810.exit', 'SourceModularFreeProductScratchOwnership810.lean', 'SourceModularFreeProductScratchOwnership810.log', 'SourceModularIrrationalAction.exit', 'SourceModularIrrationalAction.lean', 'SourceModularIrrationalAction.log', 'SourceModularPingPongSets.exit', 'SourceModularPingPongSets.lean', 'SourceModularPingPongSets.log', 'SourceModularProjectiveKernel.exit', 'SourceModularProjectiveKernel.lean', 'SourceModularProjectiveKernel.log', 'SourceUnitaryCharacterAbelianQuotient.exit', 'SourceUnitaryCharacterAbelianQuotient.lean', 'SourceUnitaryCharacterAbelianQuotient.log', 'SourceUnitaryCharacterBasisExt.exit', 'SourceUnitaryCharacterBasisExt.lean', 'SourceUnitaryCharacterBasisExt.log', 'SourceUnitaryCharacterFiniteOrder.exit', 'SourceUnitaryCharacterFiniteOrder.lean', 'SourceUnitaryCharacterFiniteOrder.log', 'SourceUnitaryCharacterLogarithm.exit', 'SourceUnitaryCharacterLogarithm.lean', 'SourceUnitaryCharacterLogarithm.log', 'SourceUnitaryCharacterRecurrence.exit', 'SourceUnitaryCharacterRecurrence.lean', 'SourceUnitaryCharacterRecurrence.log', 'SourceUnitaryCharacterTorsion.exit', 'SourceUnitaryCharacterTorsion.lean', 'SourceUnitaryCharacterTorsion.log', 'SourceUnitaryCharacterTraceBound.exit', 'SourceUnitaryCharacterTraceBound.lean', 'SourceUnitaryCharacterTraceBound.log', 'SourceUnitaryCircleCharacter.exit', 'SourceUnitaryCircleCharacter.lean', 'SourceUnitaryCircleCharacter.log', 'SourceWeightTwoClosedChainPeriods.exit', 'SourceWeightTwoClosedChainPeriods.lean', 'SourceWeightTwoClosedChainPeriods.log', 'SourceWeightTwoEndpointPeriods.exit', 'SourceWeightTwoEndpointPeriods.lean', 'SourceWeightTwoEndpointPeriods.log', 'SourceWeightTwoIntegralPeriods.exit', 'SourceWeightTwoIntegralPeriods.lean', 'SourceWeightTwoIntegralPeriods.log', 'SourceWeightTwoSegmentPeriods.exit', 'SourceWeightTwoSegmentPeriods.lean', 'SourceWeightTwoSegmentPeriods.log', 'cusp-correction-declaration-inventory-817.json', 'download_gamma_one_integral_lift_dependencies_802.py', 'download_gamma_one_period_core_796.py', 'gamma-one-closed-chain-audit-route-804.json', 'gamma-one-closed-chain-route-797.json', 'gamma-one-integral-character-correction-route-823.json', 'gamma-one-integral-character-lift-route-818.json', 'gamma-one-integral-character-modular-route-826.json', 'gamma-one-integral-lift-cusp-correction-route-811.json', 'gamma-one-integral-lift-presentation-route-805.json', 'gamma-one-meromorphic-multiplier-route-841.json', 'gamma-one-unitary-logarithm-route-831.json', 'prepare_gamma_one_closed_chain_audit_804.py', 'prepare_gamma_one_cusp_correction_811.py', 'prepare_gamma_one_integral_character_818.py', 'prepare_gamma_one_integral_character_correction_823.py', 'prepare_gamma_one_integral_character_free_product_821.py', 'prepare_gamma_one_integral_character_modular_826.py', 'prepare_gamma_one_integral_lift_presentation_805.py', 'prepare_gamma_one_meromorphic_multiplier_841.py', 'prepare_gamma_one_meromorphic_multiplier_consumer_844.py', 'prepare_gamma_one_meromorphic_multiplier_periods_audit_846.py', 'prepare_gamma_one_unitary_character_periods_audit_840.py', 'prepare_gamma_one_unitary_logarithm_836.py', 'prepare_gamma_one_unitary_logarithm_foundations_831.py', 'prepare_integral_parabolic_character_lift_audit_830.py', 'prepare_source_cusp_correction_audit_817.py', 'prepare_source_modular_free_product_audit_810.py', 'record_gamma_one_closed_chain_periods_804.py', 'record_source_cusp_correction_817.py', 'record_source_gamma_one_meromorphic_multiplier_periods_846.py', 'record_source_gamma_one_unitary_character_periods_840.py', 'record_source_gamma_one_unitary_character_periods_840b.py', 'record_source_gamma_one_unitary_character_periods_840c.py', 'record_source_integral_parabolic_character_lift_830.py', 'record_source_modular_free_product_810.py', 'record_source_modular_free_product_810b.py', 'source-cusp-correction-1-audit-config.json', 'source-cusp-correction-1-reuse-review-20261027.json', 'source-cusp-correction-1-scratch-receipt.json', 'source-cusp-correction-audit-route-817.json', 'source-gamma-one-closed-chain-periods-1-audit-config.json', 'source-gamma-one-closed-chain-periods-1-reuse-review-20261027.json', 'source-gamma-one-closed-chain-periods-1-scratch-receipt.json', 'source-gamma-one-meromorphic-multiplier-periods-1-audit-config.json', 'source-gamma-one-meromorphic-multiplier-periods-1-reuse-review-20261027.json', 'source-gamma-one-meromorphic-multiplier-periods-1-scratch-receipt.json', 'source-gamma-one-meromorphic-multiplier-periods-audit-route-846.json', 'source-gamma-one-unitary-character-periods-1-audit-config.json', 'source-gamma-one-unitary-character-periods-1-reuse-review-20261027.json', 'source-gamma-one-unitary-character-periods-1-scratch-receipt.json', 'source-gamma-one-unitary-character-periods-1b-audit-config.json', 'source-gamma-one-unitary-character-periods-1c-audit-config.json', 'source-gamma-one-unitary-character-periods-1c-reuse-review-20261027.json', 'source-gamma-one-unitary-character-periods-1c-scratch-receipt.json', 'source-gamma-one-unitary-character-periods-audit-route-840.json', 'source-integral-parabolic-character-lift-1-audit-config.json', 'source-integral-parabolic-character-lift-1-reuse-review-20261027.json', 'source-integral-parabolic-character-lift-1-scratch-receipt.json', 'source-integral-parabolic-character-lift-audit-route-830.json', 'source-modular-free-product-1-audit-config.json', 'source-modular-free-product-1-reuse-review-20261027.json', 'source-modular-free-product-1-scratch-receipt.json', 'source-modular-free-product-audit-route-810.json', 'unitary-period-registration-review-840b.json', 'unitary-period-registration-review-840c.json']]
for folder in ['cusp-correction-cyclic-cosets-failed-814a', 'gamma-one-closed-chain-periods-failed-799a', 'gamma-one-closed-chain-periods-failed-799b', 'gamma-one-closed-chain-periods-failed-799c', 'gamma-one-endpoint-periods-failed-797a', 'gamma-one-endpoint-periods-failed-797b', 'gamma-one-endpoint-periods-failed-797c', 'gamma-one-integral-periods-failed-798a', 'gamma-one-period-core-reuse-796', 'gamma-one-period-core-reuse-802', 'gamma-one-segment-periods-failed-800a', 'integral-character-initial-lift-failed-822a', 'integral-character-shapiro-failed-820a', 'integral-parabolic-character-lift-failed-828a', 'modular-free-product-lint-failed-810a', 'unitary-character-finite-order-failed-831a']:
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
supplemental_review_path=r/archive_rel/'gamma-one-multiplier-periods-promotion-route-847.json'

audit = r / "Extension/Dubon2026/Audit.lean"
at = audit.read_text(encoding="utf-8")
for n in queries:
    assert not re.search(r"``" + re.escape(n) + r"(?=[,\s])", at)
tm, dm = "\n]\n\nprivate def publicConstructions", "\n]\n\nprivate def runAudit"
assert at.count(tm) == at.count(dm) == 1
at = at.replace(tm, "".join("\n  ,``" + n for n in theorems) + tm, 1)
at = at.replace(dm, "".join("\n  ," + chr(96)*2 + n for n in defs) + dm, 1)
research_path = r / "Tools/lean-reuse-audit-20261020.json"
reuse_path = r / "Tools/source-gamma-one-multiplier-periods.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt8632"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> arithmetic realization of original finite Gamma1 homogeneous-coefficient Hecke characters -> full/parabolic, transpose, diamond, Picard/H1 comparison -> actual differential and period geometry -> Abel-Jacobi principal-divisor converse.'
discharged = 'Actual closed integer chains in the original Gamma1 orbit quotient have periods in the actual integral period lattice, with literal segment integrals. Every finite-index modular subgroup has an integral parabolic lift of each ZMod n parabolic character vanishing on finite-order elements, for every natural n including zero. The actual projective modular group is identified with C2*C3; native scalar Shapiro and transfer arguments and actual cusp-character correction construct the lift. This eliminates the torsion factors of the actual parabolic abelianization and yields a real additive logarithm of each unitary character trivial on elliptic/parabolic elements. For an ACTUAL meromorphic function with original Gamma1 divisor orders and nonzero translated cusp limits, multiplicativity and elliptic/parabolic triviality are derived, and its specific unitary multiplier is realized by actual weight-two cusp-form real periods. The signed stabilizer ramification normalization retains every nonzero level. No closed-chain period theorem, modular presentation, integral lift, cusp correction, logarithm, torsion-free quotient, multiplier character law/triviality or cusp-form-realization premise remains in these consumers.'
boundary = 'Analytic reciprocity and construction of meromorphic functions from the original Abel-Jacobi period condition remain. The meromorphic-multiplier consumer assumes the actual meromorphic function, its original divisor orders, unit-modulus multiplier and nonzero translated cusp limits; it does not construct that function. Global integral period/Picard, Hecke/diamond/H1, full/parabolic and transpose comparisons remain. Arithmetic realization of original finite homogeneous-coefficient Gamma1 characters, coefficient-field transport, Frobenius/inertia, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain. Complex semisimplicity, finite characters, Witt coefficients and universal deformation rings do not supply a characteristic-zero lift. 16/20; DUB-17--20 OPEN; all twenty gates unchanged.'
status = 'The forty-two-module original Gamma1 period and multiplier scope passes 273 public axiom queries, 352 exhaustive scratch theorem checks, sixteen linters per module and six declaration-value audits with 350 required dependency checks, with zero diagnostics. Production aggregate, focused audits and sequential foundation/paper verification of the 8,674-module scope are pending.'
route = 'The October 27 search is converted into checked local reuse. Existing equivariant primitives and native Finsupp quotient evaluation shorten the closed-chain proof. Native ping-pong and modular generators supply the projective presentation. Existing cosetTransition multiplication replaces external coset-coordinate infrastructure. Native transfer proves the cusp sum; actual finite edge chains correct it. Native Cayley-Hamilton replaces entrywise matrix expansion, native finite abelian decomposition supplies coordinates, and native UpperHalfPlane.fixedPt replaces an explicit square-root fixed-point argument. Existing signed parabolic classification, Mobius germs, exact original Gamma1 ramification and real-period surjectivity are consumed. The unused external auxiliary branches, compatibility shims, linter suppression and external import closures are not imported. Only project imports are qualified on promotion; all audited mathematical bodies remain identical. Root pins, proof limits and the source contract are unchanged.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Actual Gamma1 closed-chain periods and meromorphic multiplier realization (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 8,632-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
corrections = []
count = sum(z['exhaustiveTheorems'] for z in certs)
assert count == 352

docpaths = list(dict.fromkeys(r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]))
for f in docpaths:
    assert "\n\n" in f.read_text(encoding="utf-8")
readmes = [(r.parent / "README.md", "Current Project 83 status ("), (repo / "README.md", "Project 83 has an ")]
for f, prefix in readmes:
    assert sum(line.startswith(prefix) for line in f.read_text(encoding="utf-8").splitlines()) == 1
arch = r / "Dubon Architecture.md"
edge = '  GAMMAONEREALPERIOD8632["Every original Gamma1 real parabolic character realized by actual weight-two cusp periods. Reciprocity, Picard/Hecke/diamond/H1, all-weight arithmetic association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourceGammaOneMultiplierPeriodsProductionAudit8674.lean',p/'source-gamma-one-multiplier-periods-8674-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production8674.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/gamma-one-real-period-surjectivity-20261027-794'
registered = {row['path'] for row in c['files']}
for priorFile in priorArchive.iterdir():
    rel = priorFile.relative_to(r).as_posix()
    if priorFile.is_file() and rel not in registered:
        c['files'].append({'path': rel, 'role': 'Tools'})

reportSource = p / 'Dubon Period and Multiplier Reuse Assessment 2026-10-27.md'
assert sha(reportSource) == '8497851AF82493F3F1025005CF0C4FC125D5DFD364647DC516FFA6193F51602D'
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
    "productionModules": 8674, "modules": newmods, "queries": queries,
    "theoremRegistrations": theorems, "constructionRegistrations": defs,
    "sourceHashes": {mapping[t.stem]: sha(t) for t, _ in pending}, "scratchCertificates": certs,
    "exactDependency": dependency, "assumptionsDischarged": discharged, "stillOpen": boundary,
    "status": status, "rootPinsChanged": False, "proofLimitsChanged": False,
    "promotionChanges": 'Only project scratch imports are qualified. All audited statements, proof bodies and comments remain identical. The original Gamma1 field, all nonzero levels, literal segment periods, all natural moduli, actual modular group and signed stabilizer normalization are retained.',
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
arch.write_text(arch.read_text(encoding='utf-8').replace(edge,'  GAMMAONEREALPERIOD8632["Every original Gamma1 real parabolic character realized by actual weight-two cusp periods (DUB-17/18)"] --> GAMMAONEMULTIPLIER8674\n  GAMMAONEMULTIPLIER8674["Actual closed-chain integral periods and original-divisor meromorphic multiplier realized by cusp periods. Analytic reciprocity, meromorphic construction, Picard/Hecke/H1, all-weight arithmetic association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'),encoding='utf-8')



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Actual Gamma1 closed-chain periods and meromorphic multiplier realization - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-gamma-one-multiplier-periods.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub('  logInfo m!".*"\\n', '  logInfo m!"SOURCE GAMMA ONE MULTIPLIER PERIODS AUDIT PASS: {count} theorems including private/generated declarations. Actual original Gamma1 closed-chain periods and meromorphic multiplier realization are proved. Analytic reciprocity and original arithmetic comparison remain; 16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourceGammaOneMultiplierPeriodsProductionAudit8674.lean").write_text(out, encoding="utf-8")
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
    target = p / (source.stem + "Production8674.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
(p / "source-gamma-one-multiplier-periods-8674-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 8674, "increment": 42, "queries": 273,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
