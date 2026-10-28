from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 8923
assert d["appliedSourceGammaOneArithmeticTateH1"]["receipt8923"]["exit"] == 0
assert (p / "paper-verification-8923-console.exit").read_text().strip() == "0"
assert (r/'Tools/gamma-one-arithmetic-tate-h1-20261027-1132/canonical-evidence-8923.json').exists()
key = "appliedSourceGammaOneHomogeneousParabolic"
assert key not in d
digests = {'source-gamma-one-binary-tate-h1-1-scratch-receipt.json': '2794C1AEDCCDEA2B86938EFAE3BE6968983D2CA2DCF180BCF26EC9D5EE583C39', 'source-original-parabolic-entry-1b-scratch-receipt.json': '9D5532A39D54F3A64B84A8BCB253D82824F88F08C7886DB4D5E21411F733393E', 'source-parabolic-rational-span-1-scratch-receipt.json': '34AD75DC1C8D717ACCAFC60019C84A599DED9EB452886707E679A09F93FE3D86', 'source-original-integral-parabolic-1-scratch-receipt.json': '0CA4FCFB88CD4862E5C5873E488F1370348F4FAE45EA19B2B8B34319BF16B869', 'source-primitive-parabolic-relation-1-scratch-receipt.json': '258F0D04EDFCE9C0BD948144191B128D9ACC883DE9A2D6A0B545F9C915BB2E10'}

for name, digest in digests.items():
    assert sha(p / name) == digest
certs = [json.loads((p / name).read_text(encoding="utf-8")) for name in digests]
mods = [m for z in certs for m in z["modules"]]
queries = [q for z in certs for q in z["queries"]]
theorems = [q for z in certs for q in z["theoremRegistrations"]]
defs = [q for z in certs for q in z["constructionRegistrations"]]
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (24, 24, 64, 52, 12)
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
archive_rel='Tools/gamma-one-homogeneous-parabolic-20261028-1163'
evidence=[p/'gamma-one-homogeneous-parabolic-promotion-route-1163.json']
evidence += [p/n for n in ['SourceBinaryParabolicChange.lean', 'SourceBinaryParabolicChange1141a.exit', 'SourceBinaryParabolicChange1141a.log', 'SourceBinaryParabolicChange1141b.exit', 'SourceBinaryParabolicChange1141b.log', 'SourceCocycleConjugateCoboundary.lean', 'SourceCocycleConjugateCoboundary1151a.exit', 'SourceCocycleConjugateCoboundary1151a.log', 'SourceGammaOneBinaryParabolicH1.lean', 'SourceGammaOneBinaryParabolicH11136b.exit', 'SourceGammaOneBinaryParabolicH11136b.log', 'SourceGammaOneBinaryPeriodCharacters.lean', 'SourceGammaOneBinaryPeriodCharacters1134a.exit', 'SourceGammaOneBinaryPeriodCharacters1134a.log', 'SourceGammaOneBinaryTateH1.lean', 'SourceGammaOneBinaryTateH11137b.exit', 'SourceGammaOneBinaryTateH11137b.log', 'SourceGammaOneBinaryTateH1Audit1.exit', 'SourceGammaOneBinaryTateH1Audit1.lean', 'SourceGammaOneBinaryTateH1Audit1.log', 'SourceGammaOneBinaryTateH1DependencyAudit1.exit', 'SourceGammaOneBinaryTateH1DependencyAudit1.lean', 'SourceGammaOneBinaryTateH1DependencyAudit1.log', 'SourceGammaOneBinaryTateH1ScratchOwnership1139.exit', 'SourceGammaOneBinaryTateH1ScratchOwnership1139.lean', 'SourceGammaOneBinaryTateH1ScratchOwnership1139.log', 'SourceGammaOneBinaryTateHecke.lean', 'SourceGammaOneBinaryTateHecke1138a.exit', 'SourceGammaOneBinaryTateHecke1138a.log', 'SourceGammaOneBinaryTateHecke1138b.exit', 'SourceGammaOneBinaryTateHecke1138b.log', 'SourceGammaOneCoefficientHeckeCharacters.lean', 'SourceGammaOneCoefficientHeckeCharacters1135a.exit', 'SourceGammaOneCoefficientHeckeCharacters1135a.log', 'SourceGammaOneFiniteOrderDischarge.lean', 'SourceGammaOneFiniteOrderDischarge1133a.exit', 'SourceGammaOneFiniteOrderDischarge1133a.log', 'SourceGammaOneFiniteOrderDischarge1133b.exit', 'SourceGammaOneFiniteOrderDischarge1133b.log', 'SourceGammaOneParabolicRestriction.lean', 'SourceGammaOneParabolicRestriction1142a.exit', 'SourceGammaOneParabolicRestriction1142a.log', 'SourceGammaOneParabolicRestriction1142b.exit', 'SourceGammaOneParabolicRestriction1142b.log', 'SourceGammaOneParabolicRestriction1142c.exit', 'SourceGammaOneParabolicRestriction1142c.log', 'SourceGammaOneParabolicRestriction1142d.exit', 'SourceGammaOneParabolicRestriction1142d.log', 'SourceGammaOneParabolicRestriction1142e.exit', 'SourceGammaOneParabolicRestriction1142e.log', 'SourceOriginalBinaryCuspWitnesses.lean', 'SourceOriginalBinaryCuspWitnesses1155a.exit', 'SourceOriginalBinaryCuspWitnesses1155a.log', 'SourceOriginalIntegralParabolicAudit1.exit', 'SourceOriginalIntegralParabolicAudit1.lean', 'SourceOriginalIntegralParabolicAudit1.log', 'SourceOriginalIntegralParabolicCocycleSpan.lean', 'SourceOriginalIntegralParabolicCocycleSpan1157a.exit', 'SourceOriginalIntegralParabolicCocycleSpan1157a.log', 'SourceOriginalIntegralParabolicDependencyAudit1.exit', 'SourceOriginalIntegralParabolicDependencyAudit1.lean', 'SourceOriginalIntegralParabolicDependencyAudit1.log', 'SourceOriginalIntegralParabolicH1Span.lean', 'SourceOriginalIntegralParabolicH1Span1158a.exit', 'SourceOriginalIntegralParabolicH1Span1158a.log', 'SourceOriginalIntegralParabolicH1Span1158b.exit', 'SourceOriginalIntegralParabolicH1Span1158b.log', 'SourceOriginalIntegralParabolicScratchOwnership1161.exit', 'SourceOriginalIntegralParabolicScratchOwnership1161.lean', 'SourceOriginalIntegralParabolicScratchOwnership1161.log', 'SourceOriginalParabolicEigensystem.lean', 'SourceOriginalParabolicEigensystem1145a.exit', 'SourceOriginalParabolicEigensystem1145a.log', 'SourceOriginalParabolicEntryAudit1b.exit', 'SourceOriginalParabolicEntryAudit1b.lean', 'SourceOriginalParabolicEntryAudit1b.log', 'SourceOriginalParabolicEntryDependencyAudit1b.exit', 'SourceOriginalParabolicEntryDependencyAudit1b.lean', 'SourceOriginalParabolicEntryDependencyAudit1b.log', 'SourceOriginalParabolicEntryScratchOwnership1146.lean', 'SourceOriginalParabolicEntryScratchOwnership1146b.exit', 'SourceOriginalParabolicEntryScratchOwnership1146b.lean', 'SourceOriginalParabolicEntryScratchOwnership1146b.log', 'SourceParabolicBinaryCoordinates.lean', 'SourceParabolicBinaryCoordinates1147a.exit', 'SourceParabolicBinaryCoordinates1147a.log', 'SourceParabolicBinaryH1RationalSpan.lean', 'SourceParabolicBinaryH1RationalSpan1149a.exit', 'SourceParabolicBinaryH1RationalSpan1149a.log', 'SourceParabolicBinaryH1RationalSpan1149b.exit', 'SourceParabolicBinaryH1RationalSpan1149b.log', 'SourceParabolicBinaryRationalSpan.lean', 'SourceParabolicBinaryRationalSpan1148a.exit', 'SourceParabolicBinaryRationalSpan1148a.log', 'SourceParabolicCoefficientMap.lean', 'SourceParabolicCoefficientMap1144a.exit', 'SourceParabolicCoefficientMap1144a.log', 'SourceParabolicCohomology.lean', 'SourceParabolicCohomology1140a.exit', 'SourceParabolicCohomology1140a.log', 'SourceParabolicCohomology1140b.exit', 'SourceParabolicCohomology1140b.log', 'SourceParabolicCoordinateReuseProbe1147.exit', 'SourceParabolicCoordinateReuseProbe1147.lean', 'SourceParabolicCoordinateReuseProbe1147.log', 'SourceParabolicFiniteCuspWitnesses.lean', 'SourceParabolicFiniteCuspWitnesses1152a.exit', 'SourceParabolicFiniteCuspWitnesses1152a.log', 'SourceParabolicIntegralCoordinateSpan.lean', 'SourceParabolicIntegralCoordinateSpan1156a.exit', 'SourceParabolicIntegralCoordinateSpan1156a.log', 'SourceParabolicIntegralCoordinateSpan1156b.exit', 'SourceParabolicIntegralCoordinateSpan1156b.log', 'SourceParabolicRationalSpanAudit1.exit', 'SourceParabolicRationalSpanAudit1.lean', 'SourceParabolicRationalSpanAudit1.log', 'SourceParabolicRationalSpanDependencyAudit1.exit', 'SourceParabolicRationalSpanDependencyAudit1.lean', 'SourceParabolicRationalSpanDependencyAudit1.log', 'SourceParabolicRationalSpanScratchOwnership1150.exit', 'SourceParabolicRationalSpanScratchOwnership1150.lean', 'SourceParabolicRationalSpanScratchOwnership1150.log', 'SourceParabolicUniformDenominator.lean', 'SourceParabolicUniformDenominator1154a.exit', 'SourceParabolicUniformDenominator1154a.log', 'SourceParabolicWitnessDenominators.lean', 'SourceParabolicWitnessDenominators1153a.exit', 'SourceParabolicWitnessDenominators1153a.log', 'SourcePeriodParabolicClass.lean', 'SourcePeriodParabolicClass1143a.exit', 'SourcePeriodParabolicClass1143a.log', 'SourcePeriodParabolicClass1143b.exit', 'SourcePeriodParabolicClass1143b.log', 'SourcePeriodParabolicClass1143c.exit', 'SourcePeriodParabolicClass1143c.log', 'SourcePrimitiveParabolicHeckeRelations.lean', 'SourcePrimitiveParabolicHeckeRelations1162a.exit', 'SourcePrimitiveParabolicHeckeRelations1162a.log', 'SourcePrimitiveParabolicRelationAudit1.exit', 'SourcePrimitiveParabolicRelationAudit1.lean', 'SourcePrimitiveParabolicRelationAudit1.log', 'SourcePrimitiveParabolicRelationDependencyAudit1.exit', 'SourcePrimitiveParabolicRelationDependencyAudit1.lean', 'SourcePrimitiveParabolicRelationDependencyAudit1.log', 'SourcePrimitiveParabolicRelationScratchOwnership1163.exit', 'SourcePrimitiveParabolicRelationScratchOwnership1163.lean', 'SourcePrimitiveParabolicRelationScratchOwnership1163.log', 'audit_gamma_one_binary_tate_h1_1139.ps1', 'audit_original_integral_parabolic_1161.ps1', 'audit_original_parabolic_entry_1146.ps1', 'audit_original_parabolic_entry_1146b.ps1', 'audit_parabolic_rational_span_1150.ps1', 'audit_primitive_parabolic_relation_1163.ps1', 'consumers1142-focus.log', 'consumers1142.txt', 'consumers1148-focus.log', 'consumers1148.txt', 'consumers1154-focus.log', 'consumers1154.txt', 'consumers1161-focus.log', 'consumers1161.txt', 'consumers1161b-focus.log', 'consumers1161c-focus.log', 'docs1142.py', 'docs1148.py', 'docs1154.py', 'docs1161.py', 'drafts1134.json', 'factor1134-focus.log', 'factor1135-focus.log', 'factor1136-focus.log', 'factor1137-focus.log', 'factor1137b-focus.log', 'factor1137c-focus.log', 'factor1137d-focus.log', 'factor1137e-focus.log', 'factor1137f-focus.log', 'factor1139-focus.log', 'factor1139b-focus.log', 'factor1139c-focus.log', 'factor1140-focus.log', 'factor1140b-focus.log', 'factor1141-focus.log', 'factor1142-focus.log', 'factor1142b-focus.log', 'factor1142c-focus.log', 'factor1148-focus.log', 'factor1148b-focus.log', 'factor1148c-focus.log', 'factor1148d-focus.log', 'factor1153-focus.log', 'factor1153b-focus.log', 'factor1153c-focus.log', 'factor1154-focus.log', 'factor1154b-focus.log', 'factor1157-focus.log', 'factor1157b-focus.log', 'factor1157c-focus.log', 'factor1157d-focus.log', 'fetch_reuse_candidates_1160.py', 'fetch_reuse_diffs_1160c.py', 'fetch_reuse_sources_1160b.py', 'foundation1142-console.log', 'foundation1148-console.log', 'foundation1154-console.log', 'foundation1161-console.log', 'gamma-one-homogeneous-parabolic-promotion-route-1150.json', 'gamma-one-homogeneous-parabolic-promotion-route-1163.json', 'modules1142.json', 'modules1148.json', 'modules1154.json', 'modules1161.json', 'paper1142-console.log', 'paper1148-console.log', 'paper1154-console.log', 'paper1161-console.log', 'prepare_gamma_one_binary_tate_h1_audit_1139.py', 'prepare_original_integral_parabolic_audit_1161.py', 'prepare_original_integral_span_1157.py', 'prepare_original_parabolic_entry_audit_1146.py', 'prepare_original_parabolic_entry_audit_1146b.py', 'prepare_parabolic_rational_span_audit_1150.py', 'prepare_primitive_parabolic_relation_audit_1163.py', 'record1142.py', 'record1148.py', 'record1154.py', 'record1161.py', 'record_original_integral_parabolic_1161.py', 'record_original_parabolic_entry_1146.py', 'record_original_parabolic_entry_1146b.py', 'record_parabolic_rational_span_1150.py', 'record_primitive_parabolic_relation_1163.py', 'record_source_gamma_one_binary_tate_h1_1139.py', 'reference1158-focus.log', 'reference1158b-focus.log', 'reference1159-focus.log', 'reference1159b-focus.log', 'reference1161-focus.log', 'reference1161b-focus.log', 'reference1161c-focus.log', 'reference1161d-focus.log', 'reference1161e-focus.log', 'refresh_reuse_heads_1159.py', 'refresh_reuse_heads_1159b.py', 'register1142.py', 'register1148.py', 'register1154.py', 'register1161.py', 'registrations1142.json', 'registrations1148.json', 'registrations1154.json', 'registrations1161.json', 'section1142.txt', 'section1148.txt', 'section1154.txt', 'section1161.txt', 'source-gamma-one-binary-period-reuse-1134.json', 'source-gamma-one-binary-tate-h1-1-audit-config.json', 'source-gamma-one-binary-tate-h1-1-reuse-review-20261027.json', 'source-gamma-one-binary-tate-h1-1-scratch-receipt.json', 'source-gamma-one-binary-tate-h1-audit-route-1139.json', 'source-gamma-one-finite-order-reuse-1133.json', 'source-gamma-one-finite-tate-h1-1b-scratch-receipt.json', 'source-original-integral-parabolic-1-audit-config.json', 'source-original-integral-parabolic-1-reuse-review-20261028.json', 'source-original-integral-parabolic-1-scratch-receipt.json', 'source-original-integral-parabolic-audit-route-1161.json', 'source-original-parabolic-entry-1b-audit-config.json', 'source-original-parabolic-entry-1b-reuse-review-20261028.json', 'source-original-parabolic-entry-1b-scratch-receipt.json', 'source-original-parabolic-entry-audit-route-1146.json', 'source-original-parabolic-entry-audit-route-1146b.json', 'source-original-parabolic-entry-reuse-1140.json', 'source-parabolic-integral-denominator-reuse-1151.json', 'source-parabolic-rational-span-1-audit-config.json', 'source-parabolic-rational-span-1-reuse-review-20261028.json', 'source-parabolic-rational-span-1-scratch-receipt.json', 'source-parabolic-rational-span-audit-route-1150.json', 'source-parabolic-rational-span-reuse-1147.json', 'source-primitive-parabolic-relation-1-audit-config.json', 'source-primitive-parabolic-relation-1-reuse-review-20261028.json', 'source-primitive-parabolic-relation-1-scratch-receipt.json', 'source-primitive-parabolic-relation-audit-route-1163.json', 'status1142.txt', 'status1148.txt', 'status1154.txt', 'status1161.txt']]
for folder in ['gamma-one-binary-h1-field-notation-linebreak-1136a', 'gamma-one-binary-tate-ext-explicit-maps-1137a', 'gamma-one-binary-tate-operator-ext-depth-1138a', 'gamma-one-finite-order-trace-expansion-1133a', 'gamma-one-parabolic-change-explicit-representations-1141a', 'gamma-one-parabolic-cocycle-coercions-1140a', 'gamma-one-parabolic-restriction-remove-unused-Q-1142d', 'gamma-one-parabolic-restriction-unused-level-1142c', 'gamma-one-parabolic-span-induction-context-1149a', 'gamma-one-parabolic-span-unexecuted-encoding-1148', 'gamma-one-parabolic-trace-unused-level-1142b', 'gamma-one-period-cocycle-explicit-representations-1143a', 'gamma-one-period-cocycle-native-functor-1143b', 'original-integral-parabolic-h1-1158a', 'parabolic-integral-coordinate-span-1156a', 'reuse-head-refresh-1159', 'reuse-head-refresh-1159b']:
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
supplemental_review_path=r/archive_rel/'gamma-one-homogeneous-parabolic-promotion-route-1163.json'

audit = r / "Extension/Dubon2026/Audit.lean"
at = audit.read_text(encoding="utf-8")
for n in queries:
    assert not re.search(r"``" + re.escape(n) + r"(?=[,\s])", at)
tm, dm = "\n]\n\nprivate def publicConstructions", "\n]\n\nprivate def runAudit"
assert at.count(tm) == at.count(dm) == 1
at = at.replace(tm, "".join("\n  ,``" + n for n in theorems) + tm, 1)
at = at.replace(dm, "".join("\n  ," + chr(96)*2 + n for n in defs) + dm, 1)
research_path = r / "Tools/lean-reuse-audit-20261020.json"
reuse_path = r / "Tools/source-gamma-one-homogeneous-parabolic.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt8923"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> arithmetic realization of original finite Gamma1 homogeneous-coefficient Hecke characters -> finite parabolic character descent and actual arithmetic Tate comparison -> original homogeneous coefficients, whole Hecke words, original nonzero parabolic eigenclass, integral parabolic span and integral operator relations.'
discharged = 'The actual arithmetic Gamma1 Picard Tate module dual with the original homogeneous polynomial coefficients is equivalent to the literal native parabolic H1 at Q*(p^(n+1))^2 for p>3. Finite-order vanishing follows from the existing trace bound and actual level congruences. Independently defined arithmetic Picard Hecke duals followed by the original homogeneous matrix action intertwine every original prime operator and integral Hecke word. The original primitive period class is nonzero in parabolic homogeneous-coefficient H1 with the original eigenvalues. Coefficient reduction preserves local coboundaries; the literal diagonal Gamma1 restriction sends them to zero. Rational coordinates preserve the actual whole-cusp-stabilizer witnesses. The already finite original cusp quotient and native cocycle denominator give one uniform integer clearing the cocycle and all representative witnesses; integral conjugation transports them to every cusp. Thus the original period class lies in the complex span of actual integral parabolic H1. The original Fourier character annihilates every integral Hecke word vanishing on that submodule, without assuming vanishing on full H1.'
boundary = 'The original finite character still acts on full H1; its descent to the finite parabolic operator image and the required finite congruence/saturation remain unproved. Integral parabolic spanning and characteristic-zero operator relations do not establish finite descent. Restriction landing in parabolic H1 does not assert nonvanishing or surjectivity. Diamonds, coefficient-field/Frobenius/inertia realization, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain. Finite characters do not supply a characteristic-zero lift. 16/20; DUB-17--20 OPEN; all twenty acceptance gates unchanged.'
status = 'The twenty-four-module homogeneous Tate/H1 and original integral parabolic source comparison passes 64 public axiom queries, 151 exhaustive scratch theorem checks, sixteen linters per module and five declaration-value audits with 99 required dependency checks, with zero diagnostics. Production aggregate, focused audits and sequential foundation/paper verification of the 8,947-module scope are pending.'
route = 'Reuse the October 28 fixed-revision nine-repository search and the existing native monomial basis, scalar period-lattice duality, IsBaseChange, arithmetic Picard Hecke and Hecke-word transport. The original cusp-period witness survives coefficient morphisms and rational projection. Finitely many actual cusp-orbit representatives permit uniform integral denominator clearing; the native cocycle conjugation identity transports witnesses. This avoids a new cusp-width classification, polynomial or tensor basis, and a general parabolic corestriction theory. Native finite-generator reconstruction and H1 quotient maps give the source integral span. The existing word intertwiner and actual eigenclass evaluate the integral parabolic relation directly. New TauCeti diamond/modular-curve results remain bounded research candidates, not imported proof closures. Frozen mathematical bodies are promoted by import qualification only.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Actual original homogeneous Gamma1 Tate H1 and parabolic source comparison (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 8,923-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
corrections = []
count = sum(z['exhaustiveTheorems'] for z in certs)
assert count == 151

docpaths = list(dict.fromkeys(r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]))
for f in docpaths:
    assert "\n\n" in f.read_text(encoding="utf-8")
readmes = [(r.parent / "README.md", "Current Project 83 status ("), (repo / "README.md", "Project 83 has an ")]
for f, prefix in readmes:
    assert sum(line.startswith(prefix) for line in f.read_text(encoding="utf-8").splitlines()) == 1
arch = r / "Dubon Architecture.md"
edge = '  GAMMAONEARITHTATE8923["Actual arithmetic Picard torsion descent, Tate-period and finite H1 dual Hecke comparison proved. H1 target retains parabolic and finite-order vanishing. Full/coefficient/diamond realization, all-weight association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourceGammaOneHomogeneousParabolicProductionAudit8947.lean',p/'source-gamma-one-homogeneous-parabolic-8947-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production8947.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/gamma-one-arithmetic-tate-h1-20261027-1132'
registered = {row['path'] for row in c['files']}
for priorFile in priorArchive.iterdir():
    rel = priorFile.relative_to(r).as_posix()
    if priorFile.is_file() and rel not in registered:
        c['files'].append({'path': rel, 'role': 'Tools'})

reportSource = p / 'Dubon Homogeneous Integral Parabolic Reuse Assessment 2026-10-28.md'
assert sha(reportSource) == '61544F12B38635DB1636B9AAAE8D85D977A6A44A4D18BD202468BD464345FBC6'
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
    "productionModules": 8947, "modules": newmods, "queries": queries,
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
arch.write_text(arch.read_text(encoding='utf-8').replace(edge,'  GAMMAONEARITHTATE8923["Actual arithmetic Gamma1 Picard torsion descent, Tate-period and scalar finite H1 dual Hecke comparison proved (DUB-17/18)"] --> GAMMAONEHOMOGPARAB8947\n  GAMMAONEHOMOGPARAB8947["Original homogeneous arithmetic Tate dual/parabolic H1 and whole Hecke words proved; original nonzero parabolic eigenclass, integral span and integral operator relations proved. Finite character descent, diamonds, Galois realization and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'),encoding='utf-8')



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Actual original homogeneous Gamma1 Tate H1 and parabolic source comparison - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-gamma-one-homogeneous-parabolic.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub('  logInfo m!".*"\\n', '  logInfo m!"SOURCE GAMMA ONE HOMOGENEOUS PARABOLIC AUDIT PASS: {count} theorems including private/generated declarations. Actual homogeneous Tate dual/parabolic H1 and original whole Hecke words, original parabolic eigenclass, integral span and integral operator relations. Finite character descent, diamonds and all-weight association remain; 16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourceGammaOneHomogeneousParabolicProductionAudit8947.lean").write_text(out, encoding="utf-8")
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
    target = p / (source.stem + "Production8947.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
(p / "source-gamma-one-homogeneous-parabolic-8947-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 8947, "increment": 24, "queries": 64,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
