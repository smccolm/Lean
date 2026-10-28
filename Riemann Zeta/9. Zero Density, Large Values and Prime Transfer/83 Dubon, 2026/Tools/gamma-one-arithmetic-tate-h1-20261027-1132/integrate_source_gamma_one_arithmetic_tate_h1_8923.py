from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 8867
assert d["appliedSourceGammaOnePicardHeckeComparison"]["receipt8867"]["exit"] == 0
assert (p / "paper-verification-8867-console.exit").read_text().strip() == "0"
assert (r/'Tools/gamma-one-picard-hecke-comparison-20261027-1070/canonical-evidence-8867.json').exists()
key = "appliedSourceGammaOneArithmeticTateH1"
assert key not in d
digests = {'source-gamma-one-real-parabolic-hecke-1-scratch-receipt.json': '3CD975E2308402811F0EBF5934BDF38B192A6C1950306A1DE0744086822BC51E', 'source-gamma-one-complex-tate-hecke-1-scratch-receipt.json': 'B0966A06294EEB1254D043F68C2E3750BFAF05A77F9812200C36BD6B5B064F61', 'source-gamma-one-arithmetic-picard-injectivity-1-scratch-receipt.json': '2014DBA39AD4FDA1BB362505BCE8CF4B5CB743F0E6F37F8159FC794F9A1E26DF', 'source-gamma-one-arithmetic-torsion-tate-1b-scratch-receipt.json': '29FE079EB97DB8546E8FB0E9D529227671DF54A044B782D57BF488AFD2FF4A1F', 'source-gamma-one-arithmetic-hecke-1-scratch-receipt.json': '25675B4DE3E5BF4831069124427B1F400C040668346FD4456E7D226774AE5B44', 'source-gamma-one-finite-tate-h1-1b-scratch-receipt.json': 'CFBF4E544D283384FD3E8B1EAA0EF334E81F8B6490BE4CF117A2C8E9D7067E0F'}

for name, digest in digests.items():
    assert sha(p / name) == digest
certs = [json.loads((p / name).read_text(encoding="utf-8")) for name in digests]
mods = [m for z in certs for m in z["modules"]]
queries = [q for z in certs for q in z["queries"]]
theorems = [q for z in certs for q in z["theoremRegistrations"]]
defs = [q for z in certs for q in z["constructionRegistrations"]]
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (56, 56, 178, 140, 38)
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
archive_rel='Tools/gamma-one-arithmetic-tate-h1-20261027-1132'
evidence=[p/'gamma-one-arithmetic-tate-h1-promotion-route-1132.json']
evidence += [p/n for n in ['CheckGammaOneHeckeComplexNames1122a.exit', 'CheckGammaOneHeckeComplexNames1122a.lean', 'CheckGammaOneHeckeComplexNames1122a.log', 'CheckGammaOneHeckeDivisorElaboration1121c.exit', 'CheckGammaOneHeckeDivisorElaboration1121c.lean', 'CheckGammaOneHeckeDivisorElaboration1121c.log', 'CheckGammaOneHeckeEnvironment1122b.exit', 'CheckGammaOneHeckeEnvironment1122b.lean', 'CheckGammaOneHeckeEnvironment1122b.log', 'CheckGammaOneHeckeEnvironment1122c.exit', 'CheckGammaOneHeckeEnvironment1122c.lean', 'CheckGammaOneHeckeEnvironment1122c.log', 'SourceGammaOneArithmeticHeckeAudit1.exit', 'SourceGammaOneArithmeticHeckeAudit1.lean', 'SourceGammaOneArithmeticHeckeAudit1.log', 'SourceGammaOneArithmeticHeckeDependencyAudit1.exit', 'SourceGammaOneArithmeticHeckeDependencyAudit1.lean', 'SourceGammaOneArithmeticHeckeDependencyAudit1.log', 'SourceGammaOneArithmeticHeckeScratchOwnership1124.exit', 'SourceGammaOneArithmeticHeckeScratchOwnership1124.lean', 'SourceGammaOneArithmeticHeckeScratchOwnership1124.log', 'SourceGammaOneArithmeticPeriodInclusion.lean', 'SourceGammaOneArithmeticPeriodInclusion1129a.exit', 'SourceGammaOneArithmeticPeriodInclusion1129a.log', 'SourceGammaOneArithmeticPicardInjectivityAudit1.exit', 'SourceGammaOneArithmeticPicardInjectivityAudit1.lean', 'SourceGammaOneArithmeticPicardInjectivityAudit1.log', 'SourceGammaOneArithmeticPicardInjectivityDependencyAudit1.exit', 'SourceGammaOneArithmeticPicardInjectivityDependencyAudit1.lean', 'SourceGammaOneArithmeticPicardInjectivityDependencyAudit1.log', 'SourceGammaOneArithmeticPicardInjectivityScratchOwnership1098.exit', 'SourceGammaOneArithmeticPicardInjectivityScratchOwnership1098.lean', 'SourceGammaOneArithmeticPicardInjectivityScratchOwnership1098.log', 'SourceGammaOneArithmeticTateFiniteH1.lean', 'SourceGammaOneArithmeticTateFiniteH11130a.exit', 'SourceGammaOneArithmeticTateFiniteH11130a.log', 'SourceGammaOneArithmeticTateFiniteHecke.lean', 'SourceGammaOneArithmeticTateFiniteHecke1131a.exit', 'SourceGammaOneArithmeticTateFiniteHecke1131a.log', 'SourceGammaOneArithmeticTateHecke.lean', 'SourceGammaOneArithmeticTateHecke1123a.exit', 'SourceGammaOneArithmeticTateHecke1123a.log', 'SourceGammaOneArithmeticTatePeriods.lean', 'SourceGammaOneArithmeticTatePeriods1113a.exit', 'SourceGammaOneArithmeticTatePeriods1113a.log', 'SourceGammaOneArithmeticTorsionTateAudit1.exit', 'SourceGammaOneArithmeticTorsionTateAudit1.lean', 'SourceGammaOneArithmeticTorsionTateAudit1.log', 'SourceGammaOneArithmeticTorsionTateDependencyAudit1b.exit', 'SourceGammaOneArithmeticTorsionTateDependencyAudit1b.lean', 'SourceGammaOneArithmeticTorsionTateDependencyAudit1b.log', 'SourceGammaOneArithmeticTorsionTateScratchOwnership1114.exit', 'SourceGammaOneArithmeticTorsionTateScratchOwnership1114.lean', 'SourceGammaOneArithmeticTorsionTateScratchOwnership1114.log', 'SourceGammaOneComplexCoefficientMap.lean', 'SourceGammaOneComplexCoefficientMap1080a.exit', 'SourceGammaOneComplexCoefficientMap1080a.log', 'SourceGammaOneComplexCoefficientMap1080b.exit', 'SourceGammaOneComplexCoefficientMap1080b.log', 'SourceGammaOneComplexConstantAutomorphisms.lean', 'SourceGammaOneComplexConstantAutomorphisms1099a.exit', 'SourceGammaOneComplexConstantAutomorphisms1099a.log', 'SourceGammaOneComplexCoordinateBasis.lean', 'SourceGammaOneComplexCoordinateBasis1092a.exit', 'SourceGammaOneComplexCoordinateBasis1092a.log', 'SourceGammaOneComplexCoordinateTrace.lean', 'SourceGammaOneComplexCoordinateTrace1093a.exit', 'SourceGammaOneComplexCoordinateTrace1093a.log', 'SourceGammaOneComplexFieldExtension.lean', 'SourceGammaOneComplexFieldExtension1081a.exit', 'SourceGammaOneComplexFieldExtension1081a.log', 'SourceGammaOneComplexFieldExtension1081b.exit', 'SourceGammaOneComplexFieldExtension1081b.log', 'SourceGammaOneComplexFieldIndependence.lean', 'SourceGammaOneComplexFieldIndependence1082a.exit', 'SourceGammaOneComplexFieldIndependence1082a.log', 'SourceGammaOneComplexPicardInjectivity.lean', 'SourceGammaOneComplexPicardInjectivity1097a.exit', 'SourceGammaOneComplexPicardInjectivity1097a.log', 'SourceGammaOneComplexPicardMap.lean', 'SourceGammaOneComplexPicardMap1088a.exit', 'SourceGammaOneComplexPicardMap1088a.log', 'SourceGammaOneComplexSpanDescent.lean', 'SourceGammaOneComplexSpanDescent1095a.exit', 'SourceGammaOneComplexSpanDescent1095a.log', 'SourceGammaOneComplexSpanSeparation.lean', 'SourceGammaOneComplexSpanSeparation1083a.exit', 'SourceGammaOneComplexSpanSeparation1083a.log', 'SourceGammaOneComplexTateHecke.lean', 'SourceGammaOneComplexTateHecke1078a.exit', 'SourceGammaOneComplexTateHecke1078a.log', 'SourceGammaOneComplexTateHeckeAudit1.exit', 'SourceGammaOneComplexTateHeckeAudit1.lean', 'SourceGammaOneComplexTateHeckeAudit1.log', 'SourceGammaOneComplexTateHeckeDependencyAudit1.exit', 'SourceGammaOneComplexTateHeckeDependencyAudit1.lean', 'SourceGammaOneComplexTateHeckeDependencyAudit1.log', 'SourceGammaOneComplexTateHeckeScratchOwnership1079.exit', 'SourceGammaOneComplexTateHeckeScratchOwnership1079.lean', 'SourceGammaOneComplexTateHeckeScratchOwnership1079.log', 'SourceGammaOneComplexTatePeriods.lean', 'SourceGammaOneComplexTatePeriods1076a.exit', 'SourceGammaOneComplexTatePeriods1076a.log', 'SourceGammaOneComplexTorsionFinite.lean', 'SourceGammaOneComplexTorsionFinite1089a.exit', 'SourceGammaOneComplexTorsionFinite1089a.log', 'SourceGammaOneComplexTranslations.lean', 'SourceGammaOneComplexTranslations1100a.exit', 'SourceGammaOneComplexTranslations1100a.log', 'SourceGammaOneConstantFieldPlaces.lean', 'SourceGammaOneConstantFieldPlaces1085a.exit', 'SourceGammaOneConstantFieldPlaces1085a.log', 'SourceGammaOneConstantFieldValuationExtension.lean', 'SourceGammaOneConstantFieldValuationExtension1084a.exit', 'SourceGammaOneConstantFieldValuationExtension1084a.log', 'SourceGammaOneCoordinateDescent.lean', 'SourceGammaOneCoordinateDescent1094a.exit', 'SourceGammaOneCoordinateDescent1094a.log', 'SourceGammaOneDegreeBaseChange.lean', 'SourceGammaOneDegreeBaseChange1090a.exit', 'SourceGammaOneDegreeBaseChange1090a.log', 'SourceGammaOneDivisorConorm.lean', 'SourceGammaOneDivisorConorm1087a.exit', 'SourceGammaOneDivisorConorm1087a.log', 'SourceGammaOneExtendedPlaceMap.lean', 'SourceGammaOneExtendedPlaceMap1086a.exit', 'SourceGammaOneExtendedPlaceMap1086a.log', 'SourceGammaOneFiniteParabolicCharacters.lean', 'SourceGammaOneFiniteParabolicCharacters1126a.exit', 'SourceGammaOneFiniteParabolicCharacters1126a.log', 'SourceGammaOneFiniteParabolicCharacters1126b.exit', 'SourceGammaOneFiniteParabolicCharacters1126b.log', 'SourceGammaOneFiniteParabolicH1.lean', 'SourceGammaOneFiniteParabolicH11127a.exit', 'SourceGammaOneFiniteParabolicH11127a.log', 'SourceGammaOneFiniteParabolicHecke.lean', 'SourceGammaOneFiniteParabolicHecke1128a.exit', 'SourceGammaOneFiniteParabolicHecke1128a.log', 'SourceGammaOneFiniteParabolicHecke1128b.exit', 'SourceGammaOneFiniteParabolicHecke1128b.log', 'SourceGammaOneFinitePeriodLattice.lean', 'SourceGammaOneFinitePeriodLattice1075a.exit', 'SourceGammaOneFinitePeriodLattice1075a.log', 'SourceGammaOneFinitePeriodLattice1075b.exit', 'SourceGammaOneFinitePeriodLattice1075b.log', 'SourceGammaOneFinitePeriodLattice1075c.exit', 'SourceGammaOneFinitePeriodLattice1075c.log', 'SourceGammaOneFiniteTateH1Audit1.exit', 'SourceGammaOneFiniteTateH1Audit1.lean', 'SourceGammaOneFiniteTateH1Audit1.log', 'SourceGammaOneFiniteTateH1DependencyAudit1b.exit', 'SourceGammaOneFiniteTateH1DependencyAudit1b.lean', 'SourceGammaOneFiniteTateH1DependencyAudit1b.log', 'SourceGammaOneFiniteTateH1ScratchOwnership1132.exit', 'SourceGammaOneFiniteTateH1ScratchOwnership1132.lean', 'SourceGammaOneFiniteTateH1ScratchOwnership1132.log', 'SourceGammaOneFiniteTorsionAction.lean', 'SourceGammaOneFiniteTorsionAction1106a.exit', 'SourceGammaOneFiniteTorsionAction1106a.log', 'SourceGammaOneFiniteTorsionAction1106b.exit', 'SourceGammaOneFiniteTorsionAction1106b.log', 'SourceGammaOneFixedReducedDivisor.lean', 'SourceGammaOneFixedReducedDivisor1108a.exit', 'SourceGammaOneFixedReducedDivisor1108a.log', 'SourceGammaOneHeckeCharacters.lean', 'SourceGammaOneHeckeComplexDivisors.lean', 'SourceGammaOneHeckeComplexDivisors1121a.exit', 'SourceGammaOneHeckeComplexDivisors1121a.log', 'SourceGammaOneHeckeComplexDivisors1121b.exit', 'SourceGammaOneHeckeComplexDivisors1121b.log', 'SourceGammaOneHeckeComplexDivisors1121c.exit', 'SourceGammaOneHeckeComplexDivisors1121c.log', 'SourceGammaOneHeckeComplexDivisors1121d.exit', 'SourceGammaOneHeckeComplexDivisors1121d.log', 'SourceGammaOneHeckeComplexPicard.lean', 'SourceGammaOneHeckeComplexPicard1122a.exit', 'SourceGammaOneHeckeComplexPicard1122a.log', 'SourceGammaOneHeckeComplexPicard1122b.exit', 'SourceGammaOneHeckeComplexPicard1122b.log', 'SourceGammaOneHeckeComplexPicard1122c.exit', 'SourceGammaOneHeckeComplexPicard1122c.log', 'SourceGammaOneHeckeComplexPlaces.lean', 'SourceGammaOneHeckeComplexPlaces1120a.exit', 'SourceGammaOneHeckeComplexPlaces1120a.log', 'SourceGammaOneHeckeComplexPlaces1120b.exit', 'SourceGammaOneHeckeComplexPlaces1120b.log', 'SourceGammaOneHeckeConorm.lean', 'SourceGammaOneHeckeConorm1119a.exit', 'SourceGammaOneHeckeConorm1119a.log', 'SourceGammaOneHeckeConstantField.lean', 'SourceGammaOneHeckeConstantField1115a.exit', 'SourceGammaOneHeckeConstantField1115a.log', 'SourceGammaOneHeckeConstantPlaces.lean', 'SourceGammaOneHeckeConstantPlaces1118a.exit', 'SourceGammaOneHeckeConstantPlaces1118a.log', 'SourceGammaOneHeckeSpanSeparation.lean', 'SourceGammaOneHeckeSpanSeparation1116a.exit', 'SourceGammaOneHeckeSpanSeparation1116a.log', 'SourceGammaOneHeckeValuationExtension.lean', 'SourceGammaOneHeckeValuationExtension1117a.exit', 'SourceGammaOneHeckeValuationExtension1117a.log', 'SourceGammaOneIntegralCharacterFactor.lean', 'SourceGammaOneIntegralCharacterFactor1125a.exit', 'SourceGammaOneIntegralCharacterFactor1125a.log', 'SourceGammaOneIntegralCharacterFactor1125b.exit', 'SourceGammaOneIntegralCharacterFactor1125b.log', 'SourceGammaOneInvariantSupport.lean', 'SourceGammaOneInvariantSupport1109a.exit', 'SourceGammaOneInvariantSupport1109a.log', 'SourceGammaOneNewCoordinatePlaces.lean', 'SourceGammaOneNewCoordinatePlaces1091a.exit', 'SourceGammaOneNewCoordinatePlaces1091a.log', 'SourceGammaOneOffImageValues.lean', 'SourceGammaOneOffImageValues1101a.exit', 'SourceGammaOneOffImageValues1101a.log', 'SourceGammaOneOffImageValues1101b.exit', 'SourceGammaOneOffImageValues1101b.log', 'SourceGammaOnePeriodTateHecke.lean', 'SourceGammaOnePeriodTateHecke1077a.exit', 'SourceGammaOnePeriodTateHecke1077a.log', 'SourceGammaOnePeriodTateHecke1077b.exit', 'SourceGammaOnePeriodTateHecke1077b.log', 'SourceGammaOnePrincipalDescent.lean', 'SourceGammaOnePrincipalDescent1096a.exit', 'SourceGammaOnePrincipalDescent1096a.log', 'SourceGammaOnePrincipalDivisorIdentities.lean', 'SourceGammaOnePrincipalDivisorIdentities1105a.exit', 'SourceGammaOnePrincipalDivisorIdentities1105a.log', 'SourceGammaOnePrincipalDivisors.lean', 'SourceGammaOnePrincipalDivisors1104a.exit', 'SourceGammaOnePrincipalDivisors1104a.log', 'SourceGammaOneRealCharacterHecke1071a.exit', 'SourceGammaOneRealCharacterHecke1071a.log', 'SourceGammaOneRealCharacterHecke1071b.exit', 'SourceGammaOneRealCharacterHecke1071b.log', 'SourceGammaOneRealCharacterHecke1071c.exit', 'SourceGammaOneRealCharacterHecke1071c.log', 'SourceGammaOneRealParabolicH1.lean', 'SourceGammaOneRealParabolicH11072a.exit', 'SourceGammaOneRealParabolicH11072a.log', 'SourceGammaOneRealParabolicHecke.lean', 'SourceGammaOneRealParabolicHecke1073a.exit', 'SourceGammaOneRealParabolicHecke1073a.log', 'SourceGammaOneRealParabolicHecke1073b.exit', 'SourceGammaOneRealParabolicHecke1073b.log', 'SourceGammaOneRealParabolicHeckeAudit1.exit', 'SourceGammaOneRealParabolicHeckeAudit1.lean', 'SourceGammaOneRealParabolicHeckeAudit1.log', 'SourceGammaOneRealParabolicHeckeDependencyAudit1.exit', 'SourceGammaOneRealParabolicHeckeDependencyAudit1.lean', 'SourceGammaOneRealParabolicHeckeDependencyAudit1.log', 'SourceGammaOneRealParabolicHeckeScratchOwnership1074.exit', 'SourceGammaOneRealParabolicHeckeScratchOwnership1074.lean', 'SourceGammaOneRealParabolicHeckeScratchOwnership1074.log', 'SourceGammaOneRealPeriodH1Hecke.lean', 'SourceGammaOneRealPeriodH1Hecke1071d.exit', 'SourceGammaOneRealPeriodH1Hecke1071d.log', 'SourceGammaOneRealPeriodH1Hecke1071e.exit', 'SourceGammaOneRealPeriodH1Hecke1071e.log', 'SourceGammaOneReducedDivisorInvariance.lean', 'SourceGammaOneReducedDivisorInvariance1107a.exit', 'SourceGammaOneReducedDivisorInvariance1107a.log', 'SourceGammaOneReducedRiemannRochSpace.lean', 'SourceGammaOneReducedRiemannRochSpace1103a.exit', 'SourceGammaOneReducedRiemannRochSpace1103a.log', 'SourceGammaOneTateComparison.lean', 'SourceGammaOneTateComparison1112a.exit', 'SourceGammaOneTateComparison1112a.log', 'SourceGammaOneTorsionComparison.lean', 'SourceGammaOneTorsionComparison1111a.exit', 'SourceGammaOneTorsionComparison1111a.log', 'SourceGammaOneTorsionDivisorDescent.lean', 'SourceGammaOneTorsionDivisorDescent1110a.exit', 'SourceGammaOneTorsionDivisorDescent1110a.log', 'SourceGammaOneTranslationOrbits.lean', 'SourceGammaOneTranslationOrbits1102a.exit', 'SourceGammaOneTranslationOrbits1102a.log', 'SourceGammaOneTranslationOrbits1102b.exit', 'SourceGammaOneTranslationOrbits1102b.log', 'admissibility1126-focus.log', 'admissibility1126b-focus.log', 'admissibility1129-focus.log', 'admissibility1129b-focus.log', 'audit_gamma_one_arithmetic_hecke_1124.ps1', 'audit_gamma_one_arithmetic_picard_injectivity_1098.ps1', 'audit_gamma_one_arithmetic_torsion_tate_1114.ps1', 'audit_gamma_one_arithmetic_torsion_tate_1114b.ps1', 'audit_gamma_one_complex_tate_hecke_1079.ps1', 'audit_gamma_one_finite_tate_h1_1132.ps1', 'audit_gamma_one_finite_tate_h1_1132b.ps1', 'audit_gamma_one_real_parabolic_hecke_1074.ps1', 'consumers1074.txt', 'consumers1085.txt', 'consumers1107-focus.log', 'consumers1107.txt', 'consumers1113-focus.log', 'consumers1113.txt', 'consumers1129-focus.log', 'consumers1129.txt', 'docs1074.py', 'docs1085.py', 'docs1107.py', 'docs1113.py', 'docs1129.py', 'drafts1085.json', 'drafts1093.json', 'drafts1111.json', 'drafts1120.json', 'foundation1074-console.log', 'foundation1085-console.log', 'foundation1107-console.log', 'foundation1113-console.log', 'foundation1129-console.log', 'gamma-one-arithmetic-tate-h1-promotion-route-1132.json', 'modules1074.json', 'modules1085.json', 'modules1107.json', 'modules1113.json', 'modules1129.json', 'paper1074-console.log', 'paper1085-console.log', 'paper1107-console.log', 'paper1113-console.log', 'paper1129-console.log', 'prepare_gamma_one_arithmetic_hecke_audit_1124.py', 'prepare_gamma_one_arithmetic_picard_injectivity_audit_1098.py', 'prepare_gamma_one_arithmetic_torsion_tate_audit_1114.py', 'prepare_gamma_one_complex_tate_hecke_audit_1079.py', 'prepare_gamma_one_finite_tate_h1_audit_1132.py', 'prepare_gamma_one_real_parabolic_hecke_audit_1074.py', 'record1074.py', 'record1085.py', 'record1107.py', 'record1113.py', 'record1129.py', 'record_source_gamma_one_arithmetic_hecke_1124.py', 'record_source_gamma_one_arithmetic_picard_injectivity_1098.py', 'record_source_gamma_one_arithmetic_torsion_tate_1114.py', 'record_source_gamma_one_arithmetic_torsion_tate_1114b.py', 'record_source_gamma_one_complex_tate_hecke_1079.py', 'record_source_gamma_one_finite_tate_h1_1132.py', 'record_source_gamma_one_finite_tate_h1_1132b.py', 'record_source_gamma_one_real_parabolic_hecke_1074.py', 'register1074.py', 'register1085.py', 'register1107.py', 'register1113.py', 'register1129.py', 'registrations1074.json', 'registrations1085.json', 'registrations1107.json', 'registrations1113.json', 'registrations1129.json', 'section1074.txt', 'section1085.txt', 'section1107.txt', 'section1113.txt', 'section1129.txt', 'source-gamma-one-analytic-abel-kernel-1-scratch-receipt.json', 'source-gamma-one-arithmetic-complex-route-1080.json', 'source-gamma-one-arithmetic-dual-reuse-1129.json', 'source-gamma-one-arithmetic-hecke-1-audit-config.json', 'source-gamma-one-arithmetic-hecke-1-reuse-review-20261027.json', 'source-gamma-one-arithmetic-hecke-1-scratch-receipt.json', 'source-gamma-one-arithmetic-hecke-audit-route-1124.json', 'source-gamma-one-arithmetic-hecke-route-1115.json', 'source-gamma-one-arithmetic-picard-injectivity-1-audit-config.json', 'source-gamma-one-arithmetic-picard-injectivity-1-reuse-review-20261027.json', 'source-gamma-one-arithmetic-picard-injectivity-1-scratch-receipt.json', 'source-gamma-one-arithmetic-picard-injectivity-audit-route-1098.json', 'source-gamma-one-arithmetic-torsion-tate-1b-audit-config.json', 'source-gamma-one-arithmetic-torsion-tate-1b-reuse-review-20261027.json', 'source-gamma-one-arithmetic-torsion-tate-1b-scratch-receipt.json', 'source-gamma-one-arithmetic-torsion-tate-audit-route-1114.json', 'source-gamma-one-arithmetic-torsion-tate-audit-route-1114b.json', 'source-gamma-one-character-coefficient-route-1071c.json', 'source-gamma-one-complex-tate-hecke-1-audit-config.json', 'source-gamma-one-complex-tate-hecke-1-reuse-review-20261027.json', 'source-gamma-one-complex-tate-hecke-1-scratch-receipt.json', 'source-gamma-one-complex-tate-hecke-audit-route-1079.json', 'source-gamma-one-finite-parabolic-route-1125.json', 'source-gamma-one-finite-tate-h1-1b-audit-config.json', 'source-gamma-one-finite-tate-h1-1b-reuse-review-20261027.json', 'source-gamma-one-finite-tate-h1-1b-scratch-receipt.json', 'source-gamma-one-finite-tate-h1-audit-route-1132.json', 'source-gamma-one-finite-tate-h1-audit-route-1132b.json', 'source-gamma-one-hecke-analytic-maps-1-scratch-receipt.json', 'source-gamma-one-hecke-geometric-fibers-1b-scratch-receipt.json', 'source-gamma-one-hecke-primitive-trace-1-scratch-receipt.json', 'source-gamma-one-holomorphic-h1-hecke-1-scratch-receipt.json', 'source-gamma-one-period-lattice-hecke-1b-scratch-receipt.json', 'source-gamma-one-period-tate-route-1075.json', 'source-gamma-one-picard-period-equivalence-1d-scratch-receipt.json', 'source-gamma-one-picard-period-hecke-1-scratch-receipt.json', 'source-gamma-one-principal-descent-route-1090.json', 'source-gamma-one-real-h1-direct-route-1071d.json', 'source-gamma-one-real-parabolic-hecke-1-audit-config.json', 'source-gamma-one-real-parabolic-hecke-1-reuse-review-20261027.json', 'source-gamma-one-real-parabolic-hecke-1-scratch-receipt.json', 'source-gamma-one-real-parabolic-hecke-audit-route-1074.json', 'source-gamma-one-real-parabolic-hecke-route-1071.json', 'source-gamma-one-span-descent-reuse-1083.json', 'source-gamma-one-torsion-descent-route-1099.json', 'status-before1074.txt', 'status1074.txt', 'status1085.txt', 'status1107.txt', 'status1113.txt', 'status1129.txt', 'sublevel1120-focus.log', 'sublevel1121-focus.log', 'sublevel1121b-focus.log', 'sublevel1124-focus.log', 'sublevel1124b-focus.log', 'sublevel1124c-focus.log']]
for folder in ['gamma-one-character-coordinate-third-whnf-1071c', 'gamma-one-coefficient-embedding-name-1080a', 'gamma-one-complex-field-lift-rewrite-1081a', 'gamma-one-finite-characters-smul-binder-1126a', 'gamma-one-finite-h1-all-index-consumer-audit-1132a', 'gamma-one-finite-h1-hecke-character-rewrite-1128a', 'gamma-one-hecke-divisors-incomplete-elaboration-1121a', 'gamma-one-hecke-divisors-missing-correspondence-import-1121b', 'gamma-one-hecke-divisors-universe-elaboration-1121c', 'gamma-one-hecke-picard-alias-rewrite-1122b', 'gamma-one-hecke-picard-unavailable-divisor-declarations-1122a', 'gamma-one-hecke-restriction-consumer-name-1120a', 'gamma-one-integral-factor-lattice-coercions-1125a', 'gamma-one-j-value-unused-level-1101a', 'gamma-one-lattice-notation-projection-1075a', 'gamma-one-lattice-range-instance-1075b', 'gamma-one-parabolic-range-subtype-1073a', 'gamma-one-period-quotient-notation-1077a', 'gamma-one-real-character-coordinates-whnf-1071b', 'gamma-one-real-character-whnf-1071a', 'gamma-one-real-period-finite-cosets-1071d', 'gamma-one-tate-transparent-accessor-value-1114a', 'gamma-one-torsion-action-picard-name-1106a', 'gamma-one-translation-orbit-beta-reduction-1102a']:
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
supplemental_review_path=r/archive_rel/'gamma-one-arithmetic-tate-h1-promotion-route-1132.json'

audit = r / "Extension/Dubon2026/Audit.lean"
at = audit.read_text(encoding="utf-8")
for n in queries:
    assert not re.search(r"``" + re.escape(n) + r"(?=[,\s])", at)
tm, dm = "\n]\n\nprivate def publicConstructions", "\n]\n\nprivate def runAudit"
assert at.count(tm) == at.count(dm) == 1
at = at.replace(tm, "".join("\n  ,``" + n for n in theorems) + tm, 1)
at = at.replace(dm, "".join("\n  ," + chr(96)*2 + n for n in defs) + dm, 1)
research_path = r / "Tools/lean-reuse-audit-20261020.json"
reuse_path = r / "Tools/source-gamma-one-arithmetic-tate-h1.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt8867"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> arithmetic realization of original finite Gamma1 homogeneous-coefficient Hecke characters -> full/parabolic, transpose, diamond and arithmetic Picard/H1 comparison -> actual finite arithmetic Tate dual and native H1 Hecke comparison.'
discharged = 'The actual arithmetic Gamma1 Picard group injects into the complex Picard group, and every nonzero-modulus complex torsion class descends. The resulting arithmetic-to-complex Tate equivalence preserves the actual Hecke operators. Its composition with the original Picard-period equivalence identifies the arithmetic Tate module with the p-adic tensor of the original finite free integral-period lattice. Prime Hecke operators act by the actual dual cusp operator, including primes dividing the level. Integer parabolic characters factor through that lattice by the proved real-period surjectivity. The proved integral lift gives an equivalence between its modulus dual and the literal native H1 submodule whose characters vanish on parabolic and finite-order elements. Native base-change universality identifies this same H1 submodule with finite characters of the actual arithmetic Tate module. This equivalence intertwines arithmetic Picard prime Hecke duals and native H1 Hecke operators. The real parabolic H1 comparison and stability are also proved. No arithmetic torsion descent, Tate comparison, lattice-dual realization or Hecke compatibility premise remains in these stated comparisons.'
boundary = 'The finite H1 target explicitly retains parabolic and finite-order vanishing. The full/parabolic passage, discharge of finite-order vanishing for the application, original homogeneous coefficients and diamonds, coefficient-field/Frobenius/inertia realization, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain. No rank-equals-twice-genus claim is inferred from the lattice-rank torsion cardinality. Finite characters do not supply a characteristic-zero lift. 16/20; DUB-17--20 OPEN; all twenty acceptance gates unchanged.'
status = 'The fifty-six-module arithmetic Tate and finite H1 comparison passes 178 public axiom queries, 357 exhaustive scratch theorem checks, sixteen linters per module and six declaration-value audits with 207 required dependency checks, with zero diagnostics. Production aggregate, focused audits and sequential foundation/paper verification of the 8,923-module scope are pending.'
route = 'Reuse the fixed-revision October 27 search and proved local arithmetic curves, constant-field places, finite Riemann-Roch spaces, period surjectivity, integral character lifting and native tensor universal properties. Coefficient-span descent and equality of coordinate degrees prove Picard injectivity; finite torsion actions and translation orbits prove torsion descent. Only place extension and divisor conorm are developed for the Hecke intersection field. The finite H1 route factors integer characters through the actual period kernel and uses the existing integral lift, avoiding a second integral Poincare-duality argument. IsBaseChange from the proved arithmetic Tate equivalence avoids a new tensor basis construction. Frozen mathematical bodies are promoted by import qualification only.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Actual original Gamma1 arithmetic Tate and finite H1 comparison (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 8,867-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
corrections = []
count = sum(z['exhaustiveTheorems'] for z in certs)
assert count == 357

docpaths = list(dict.fromkeys(r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]))
for f in docpaths:
    assert "\n\n" in f.read_text(encoding="utf-8")
readmes = [(r.parent / "README.md", "Current Project 83 status ("), (repo / "README.md", "Project 83 has an ")]
for f, prefix in readmes:
    assert sum(line.startswith(prefix) for line in f.read_text(encoding="utf-8").splitlines()) == 1
arch = r / "Dubon Architecture.md"
edge = '  GAMMAONEPICARDHECKE8867["Actual complex Picard-period equivalence, holomorphic H1 Hecke compatibility and literal prime Picard Hecke compatibility proved. Full parabolic, diamond, transpose, arithmetic, all-weight association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourceGammaOneArithmeticTateH1ProductionAudit8923.lean',p/'source-gamma-one-arithmetic-tate-h1-8923-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production8923.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/gamma-one-picard-hecke-comparison-20261027-1070'
registered = {row['path'] for row in c['files']}
for priorFile in priorArchive.iterdir():
    rel = priorFile.relative_to(r).as_posix()
    if priorFile.is_file() and rel not in registered:
        c['files'].append({'path': rel, 'role': 'Tools'})

reportSource = p / 'Dubon Arithmetic Tate H1 Reuse Assessment 2026-10-27.md'
assert sha(reportSource) == '832A831DF28D4D14038115E3BCBAD0291E01FF4DD66DA29CBAD8FF00C99F2639'
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
    "productionModules": 8923, "modules": newmods, "queries": queries,
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
arch.write_text(arch.read_text(encoding='utf-8').replace(edge,'  GAMMAONEPICARDHECKE8867["Actual complex Gamma1 Picard-period and prime Hecke comparison proved (DUB-17/18)"] --> GAMMAONEARITHTATE8923\n  GAMMAONEARITHTATE8923["Actual arithmetic Picard torsion descent, Tate-period and finite H1 dual Hecke comparison proved. H1 target retains parabolic and finite-order vanishing. Full/coefficient/diamond realization, all-weight association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'),encoding='utf-8')



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Actual original Gamma1 arithmetic Tate and finite H1 comparison - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-gamma-one-arithmetic-tate-h1.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub('  logInfo m!".*"\\n', '  logInfo m!"SOURCE GAMMA ONE ARITHMETIC TATE H1 AUDIT PASS: {count} theorems including private/generated declarations. Actual arithmetic torsion descent, Tate-period and finite H1 dual Hecke comparison. Full/parabolic passage, homogeneous coefficients, diamonds and all-weight association remain; 16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourceGammaOneArithmeticTateH1ProductionAudit8923.lean").write_text(out, encoding="utf-8")
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
    target = p / (source.stem + "Production8923.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
(p / "source-gamma-one-arithmetic-tate-h1-8923-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 8923, "increment": 56, "queries": 178,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
