from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 9007
assert d["appliedSourceArithmeticDiamondComparison"]["receipt9007"]["exit"] == 0
assert (p / "paper-verification-9007-console.exit").read_text().strip() == "0"
assert (r/'Tools/arithmetic-diamond-comparison-20261028-1241/canonical-evidence-9007.json').exists()
key = "appliedSourceFrobeniusDiamond"
assert key not in d
digests = {'source-frobenius-normalization-1-scratch-receipt.json': '66C74A6E560692ACA8206D17FCDAD617AAC4C9565A86C6BDCE805D31A9FB2957', 'source-diamond-transfer-1-scratch-receipt.json': '951FAB13BC6D856AD1E24F9672859DCBE24635DE047C1680FED402F203A35DD2', 'source-hecke-diamond-character-1-scratch-receipt.json': '234287D26314603BA5CF98454727CDCA506B573E8C49E4E92B3057368D0224B6'}

for name, digest in digests.items():
    assert sha(p / name) == digest
certs = [json.loads((p / name).read_text(encoding="utf-8")) for name in digests]
mods = [m for z in certs for m in z["modules"]]
queries = [q for z in certs for q in z["queries"]]
theorems = [q for z in certs for q in z["theoremRegistrations"]]
defs = [q for z in certs for q in z["constructionRegistrations"]]
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (19, 19, 42, 27, 15)
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
archive_rel='Tools/frobenius-diamond-20261028-1267'
evidence=[p/'frobenius-diamond-promotion-route-1267.json']
evidence += [p/n for n in ['SourceCoefficientDualAction.lean', 'SourceCoefficientDualAction1249a.exit', 'SourceCoefficientDualAction1249a.log', 'SourceCoefficientDualAction1249b.exit', 'SourceCoefficientDualAction1249b.log', 'SourceDiamondTransferAudit1.exit', 'SourceDiamondTransferAudit1.lean', 'SourceDiamondTransferAudit1.log', 'SourceDiamondTransferDependencyAudit1.exit', 'SourceDiamondTransferDependencyAudit1.lean', 'SourceDiamondTransferDependencyAudit1.log', 'SourceDiamondTransferScratchOwnership1262.exit', 'SourceDiamondTransferScratchOwnership1262.lean', 'SourceDiamondTransferScratchOwnership1262.log', 'SourceFrobeniusNormalizationAudit1.exit', 'SourceFrobeniusNormalizationAudit1.lean', 'SourceFrobeniusNormalizationAudit1.log', 'SourceFrobeniusNormalizationDependencyAudit1.exit', 'SourceFrobeniusNormalizationDependencyAudit1.lean', 'SourceFrobeniusNormalizationDependencyAudit1.log', 'SourceFrobeniusNormalizationScratchOwnership1250.exit', 'SourceFrobeniusNormalizationScratchOwnership1250.lean', 'SourceFrobeniusNormalizationScratchOwnership1250.log', 'SourceGammaOneArithmeticTateOperators.lean', 'SourceGammaOneArithmeticTateOperators1246a.exit', 'SourceGammaOneArithmeticTateOperators1246a.log', 'SourceGammaOneBinaryFrobeniusNormalization.lean', 'SourceGammaOneBinaryFrobeniusNormalization1245a.exit', 'SourceGammaOneBinaryFrobeniusNormalization1245a.log', 'SourceGammaOneBinaryFrobeniusNormalization1245b.exit', 'SourceGammaOneBinaryFrobeniusNormalization1245b.log', 'SourceGammaOneBinaryFrobeniusNormalization1245c.exit', 'SourceGammaOneBinaryFrobeniusNormalization1245c.log', 'SourceGammaOneBinaryFrobeniusNormalization1245d.exit', 'SourceGammaOneBinaryFrobeniusNormalization1245d.log', 'SourceGammaOneBinaryFrobeniusNormalization1245e.exit', 'SourceGammaOneBinaryFrobeniusNormalization1245e.log', 'SourceGammaOneBinaryFrobeniusNormalization1245f.exit', 'SourceGammaOneBinaryFrobeniusNormalization1245f.log', 'SourceGammaOneBinaryFrobeniusNormalization1245g.exit', 'SourceGammaOneBinaryFrobeniusNormalization1245g.log', 'SourceGammaOneBinaryFrobeniusNormalization1245h.exit', 'SourceGammaOneBinaryFrobeniusNormalization1245h.log', 'SourceGammaOneBinaryGaloisHecke.lean', 'SourceGammaOneBinaryGaloisHecke1247a.exit', 'SourceGammaOneBinaryGaloisHecke1247a.log', 'SourceGammaOneBinaryGaloisHecke1247b.exit', 'SourceGammaOneBinaryGaloisHecke1247b.log', 'SourceGammaOneBinaryGaloisHecke1247c.exit', 'SourceGammaOneBinaryGaloisHecke1247c.log', 'SourceGammaOneBinaryGaloisHecke1247d.exit', 'SourceGammaOneBinaryGaloisHecke1247d.log', 'SourceGammaOneBinaryGaloisHecke1247e.exit', 'SourceGammaOneBinaryGaloisHecke1247e.log', 'SourceGammaOneBinaryGaloisHecke1247f.exit', 'SourceGammaOneBinaryGaloisHecke1247f.log', 'SourceGammaOneBinaryGaloisHecke1247g.exit', 'SourceGammaOneBinaryGaloisHecke1247g.log', 'SourceGammaOneBinaryGaloisHecke1247h.exit', 'SourceGammaOneBinaryGaloisHecke1247h.log', 'SourceGammaOneBinaryGaloisHecke1247i.exit', 'SourceGammaOneBinaryGaloisHecke1247i.log', 'SourceGammaOneBinaryGaloisHecke1247j.exit', 'SourceGammaOneBinaryGaloisHecke1247j.log', 'SourceGammaOneDiamondRange.lean', 'SourceGammaOneDiamondRange1255a.exit', 'SourceGammaOneDiamondRange1255a.log', 'SourceGammaOneDiamondSubgroupSquare.lean', 'SourceGammaOneDiamondSubgroupSquare1258a.exit', 'SourceGammaOneDiamondSubgroupSquare1258a.log', 'SourceGammaOneDiamondSubgroupSquare1258b.exit', 'SourceGammaOneDiamondSubgroupSquare1258b.log', 'SourceGammaOneDiamondSubgroupSquare1258c.exit', 'SourceGammaOneDiamondSubgroupSquare1258c.log', 'SourceGammaOneDiamondTransfer.lean', 'SourceGammaOneDiamondTransfer1259a.exit', 'SourceGammaOneDiamondTransfer1259a.log', 'SourceGammaOneDiamondTransfer1259b.exit', 'SourceGammaOneDiamondTransfer1259b.log', 'SourceGammaOneHeckeDiamondCoefficient.lean', 'SourceGammaOneHeckeDiamondCoefficient1244a.exit', 'SourceGammaOneHeckeDiamondCoefficient1244a.log', 'SourceGammaOneHeckeDiamondCoefficient1244b.exit', 'SourceGammaOneHeckeDiamondCoefficient1244b.log', 'SourceGammaOneHeckeDiamondDescent.lean', 'SourceGammaOneHeckeDiamondDescent1265a.exit', 'SourceGammaOneHeckeDiamondDescent1265a.log', 'SourceGammaOneHeckeDiamondWords.lean', 'SourceGammaOneHeckeDiamondWords1264a.exit', 'SourceGammaOneHeckeDiamondWords1264a.log', 'SourceH1CompositionSquare.lean', 'SourceH1CompositionSquare1260a.exit', 'SourceH1CompositionSquare1260a.log', 'SourceH1TraceInner.lean', 'SourceH1TraceInner1254a.exit', 'SourceH1TraceInner1254a.log', 'SourceH1TraceSubgroupEquality.lean', 'SourceH1TraceSubgroupEquality1256a.exit', 'SourceH1TraceSubgroupEquality1256a.log', 'SourceHeckeDiamondCharacterAudit1.exit', 'SourceHeckeDiamondCharacterAudit1.lean', 'SourceHeckeDiamondCharacterAudit1.log', 'SourceHeckeDiamondCharacterDependencyAudit1.exit', 'SourceHeckeDiamondCharacterDependencyAudit1.lean', 'SourceHeckeDiamondCharacterDependencyAudit1.log', 'SourceHeckeDiamondCharacterScratchOwnership1267.exit', 'SourceHeckeDiamondCharacterScratchOwnership1267.lean', 'SourceHeckeDiamondCharacterScratchOwnership1267.log', 'SourceHeckeWordCommutation1252a.exit', 'SourceHeckeWordCommutation1252a.log', 'SourceHomogeneousHeckeDiamond.lean', 'SourceHomogeneousHeckeDiamond1243a.exit', 'SourceHomogeneousHeckeDiamond1243a.log', 'SourceHomogeneousHeckeDiamond1243b.exit', 'SourceHomogeneousHeckeDiamond1243b.log', 'SourceInnerH1Identity.lean', 'SourceInnerH1Identity1253a.exit', 'SourceInnerH1Identity1253a.log', 'SourceInnerH1Identity1253b.exit', 'SourceInnerH1Identity1253b.log', 'SourceInnerH1Identity1253c.exit', 'SourceInnerH1Identity1253c.log', 'SourceInnerH1Identity1253d.exit', 'SourceInnerH1Identity1253d.log', 'SourceNormalizerCoefficientValue.lean', 'SourceNormalizerCoefficientValue1261a.exit', 'SourceNormalizerCoefficientValue1261a.log', 'SourceNormalizerH1Trace.lean', 'SourceNormalizerH1Trace1257a.exit', 'SourceNormalizerH1Trace1257a.log', 'SourceNormalizerH1Trace1257b.exit', 'SourceNormalizerH1Trace1257b.log', 'SourcePrimitiveGammaOneHeckeDiamondCharacter.lean', 'SourcePrimitiveGammaOneHeckeDiamondCharacter1266a.exit', 'SourcePrimitiveGammaOneHeckeDiamondCharacter1266a.log', 'SourceTateDualQuadratic.lean', 'SourceTateDualQuadratic1248a.exit', 'SourceTateDualQuadratic1248a.log', 'SourceTateDualQuadratic1248b.exit', 'SourceTateDualQuadratic1248b.log', 'audit_diamond_transfer_1262.ps1', 'audit_frobenius_normalization_1250.ps1', 'audit_hecke_diamond_character_1267.ps1', 'compile_arithmetic_tate_operators_1246a.ps1', 'compile_binary_frobenius_normalization_1245a.ps1', 'compile_binary_frobenius_normalization_1245b.ps1', 'compile_binary_frobenius_normalization_1245c.ps1', 'compile_binary_frobenius_normalization_1245d.ps1', 'compile_binary_frobenius_normalization_1245e.ps1', 'compile_binary_frobenius_normalization_1245f.ps1', 'compile_binary_frobenius_normalization_1245g.ps1', 'compile_binary_frobenius_normalization_1245h.ps1', 'compile_binary_galois_hecke_1247a.ps1', 'compile_binary_galois_hecke_1247b.ps1', 'compile_binary_galois_hecke_1247c.ps1', 'compile_binary_galois_hecke_1247d.ps1', 'compile_binary_galois_hecke_1247e.ps1', 'compile_binary_galois_hecke_1247f.ps1', 'compile_binary_galois_hecke_1247g.ps1', 'compile_binary_galois_hecke_1247h.ps1', 'compile_binary_galois_hecke_1247i.ps1', 'compile_binary_galois_hecke_1247j.ps1', 'compile_coefficient_dual_action_1249a.ps1', 'compile_coefficient_dual_action_1249b.ps1', 'compile_gamma_one_diamond_range_1255a.ps1', 'compile_gamma_one_diamond_subgroup_square_1258a.ps1', 'compile_gamma_one_diamond_subgroup_square_1258b.ps1', 'compile_gamma_one_diamond_subgroup_square_1258c.ps1', 'compile_gamma_one_diamond_transfer_1259a.ps1', 'compile_gamma_one_diamond_transfer_1259b.ps1', 'compile_gamma_one_hecke_diamond_coefficient_1244a.ps1', 'compile_gamma_one_hecke_diamond_coefficient_1244b.ps1', 'compile_h1_composition_square_1260a.ps1', 'compile_h1_trace_inner_1254a.ps1', 'compile_h1_trace_subgroup_equality_1256a.ps1', 'compile_hecke_diamond_descent_1265a.ps1', 'compile_hecke_diamond_words_1264a.ps1', 'compile_hecke_word_commutation_1252a.ps1', 'compile_homogeneous_hecke_diamond_1243a.ps1', 'compile_homogeneous_hecke_diamond_1243b.ps1', 'compile_inner_h1_identity_1253a.ps1', 'compile_inner_h1_identity_1253b.ps1', 'compile_inner_h1_identity_1253c.ps1', 'compile_inner_h1_identity_1253d.ps1', 'compile_normalizer_coefficient_value_1261a.ps1', 'compile_normalizer_h1_trace_1257a.ps1', 'compile_normalizer_h1_trace_1257b.ps1', 'compile_primitive_diamond_character_1266a.ps1', 'compile_tate_dual_quadratic_1248a.ps1', 'compile_tate_dual_quadratic_1248b.ps1', 'consumers1251-focus.log', 'consumers1251.txt', 'consumers1267-focus.log', 'consumers1267.txt', 'create_character_audit_1267.py', 'docs1251.py', 'docs1267.py', 'fetch_followup_candidates_1251b.py', 'fetch_followup_candidates_1251c.py', 'fetch_followup_reuse_1251.py', 'foundation1251-console.log', 'foundation1267-console.log', 'frobenius-diamond-promotion-route-1267.json', 'math1267.txt', 'modules1251.json', 'modules1267.json', 'paper1251-console.log', 'paper1267-console.log', 'prepare_additional_reuse_registration_1263b.py', 'prepare_diamond_transfer_audit_1262.py', 'prepare_frobenius_normalization_audit_1250.py', 'prepare_hecke_diamond_character_audit_1267.py', 'prepare_hecke_diamond_descent_1265.py', 'prepare_primitive_diamond_character_1266.py', 'record1251.py', 'record1267.py', 'record_diamond_transfer_1262.py', 'record_frobenius_normalization_1250.py', 'record_hecke_diamond_character_1267.py', 'register1251.py', 'register1267.py', 'register_additional_reuse_1263.py', 'register_additional_reuse_1263b.py', 'registrations1251.json', 'registrations1267.json', 'remaining1251.txt', 'remaining1267.txt', 'section1251.txt', 'section1267.txt', 'source-diamond-transfer-1-audit-config.json', 'source-diamond-transfer-1-reuse-review-20261028.json', 'source-diamond-transfer-1-scratch-receipt.json', 'source-diamond-transfer-audit-route-1262.json', 'source-frobenius-normalization-1-audit-config.json', 'source-frobenius-normalization-1-reuse-review-20261028.json', 'source-frobenius-normalization-1-scratch-receipt.json', 'source-frobenius-normalization-audit-route-1250.json', 'source-hecke-diamond-character-1-audit-config.json', 'source-hecke-diamond-character-1-reuse-review-20261028.json', 'source-hecke-diamond-character-1-scratch-receipt.json', 'source-hecke-diamond-character-audit-route-1267.json', 'status1251.txt', 'status1267.txt']]
for folder in ['binary-frobenius-normalization-1245a', 'binary-frobenius-normalization-1245b', 'binary-frobenius-normalization-1245c', 'binary-frobenius-normalization-1245d', 'binary-frobenius-normalization-1245e', 'binary-frobenius-normalization-1245f', 'binary-frobenius-normalization-1245g', 'binary-galois-hecke-1247a', 'binary-galois-hecke-1247b', 'binary-galois-hecke-1247c', 'binary-galois-hecke-1247d', 'binary-galois-hecke-1247e', 'binary-galois-hecke-1247f', 'binary-galois-hecke-1247g', 'binary-galois-hecke-1247h', 'binary-galois-hecke-1247i', 'coefficient-dual-action-1249a', 'followup-reuse-1251', 'gamma-one-diamond-subgroup-square-1258a', 'gamma-one-diamond-subgroup-square-1258b', 'gamma-one-diamond-transfer-1259a', 'gamma-one-hecke-diamond-coefficient-1244a', 'homogeneous-hecke-diamond-1243a', 'inner-h1-identity-1253a', 'inner-h1-identity-1253b', 'inner-h1-identity-1253c', 'normalizer-h1-trace-1257a', 'tate-dual-quadratic-1248a']:
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
supplemental_review_path=r/archive_rel/'frobenius-diamond-promotion-route-1267.json'

audit = r / "Extension/Dubon2026/Audit.lean"
at = audit.read_text(encoding="utf-8")
for n in queries:
    assert not re.search(r"``" + re.escape(n) + r"(?=[,\s])", at)
tm, dm = "\n]\n\nprivate def publicConstructions", "\n]\n\nprivate def runAudit"
assert at.count(tm) == at.count(dm) == 1
at = at.replace(tm, "".join("\n  ,``" + n for n in theorems) + tm, 1)
at = at.replace(dm, "".join("\n  ," + chr(96)*2 + n for n in defs) + dm, 1)
research_path = r / "Tools/lean-reuse-audit-20261020.json"
reuse_path = r / "Tools/source-frobenius-diamond.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt9007"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> original finite Gamma1 homogeneous-coefficient arithmetic Hecke characters -> exact Frobenius normalization, Galois-compatible operators and original diamond-one character.'
discharged = 'The original homogeneous Hecke coefficient squared is ell^w times the actual normalizer diamond coefficient at every degree and positive modulus. The actual Gamma1 Tate Galois action commutes with the original arithmetic Hecke and diamond operators, and its genuine contragredient homogeneous-valued dual commutes with every native prime Hecke operator. Given the explicitly stated original geometric Tate relation H*F=F*F+ell*D, the original dual calculation derives the normalized relation with ell^(w+1) times the actual coefficient diamond; the geometric relation itself remains unproved. The actual native full-H1 transfer is invariant under every original normalizer diamond with its inverse homogeneous coefficient action, without a six-unit or parabolic-preimage hypothesis. Reusing the native whole-word intertwiner and surjective operator descent constructs the original primitive form character on the literal Gamma1 algebra generated by prime Hecke and actual diamond operators. For p greater than three and every p-power precision, it retains the original Fourier values and sends each original diamond to one. This character is on full H1, not yet a parabolic two-dimensional arithmetic realization.'
boundary = 'Original diamond transfer invariance and the full-H1 diamond-one finite character are proved, as are exact coefficient normalization and ambient Galois/Hecke compatibility. The Gamma1 geometric Frobenius relation remains the explicit input of the conditional normalization theorem. Original parabolic preimages or a faithful alternative, parabolic character factorization, Frobenius/inertia realization, exceptional primes, coefficient-field realization and original all-weight characteristic-zero association remain. Local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain. An ambient Galois representation and finite characters do not supply a two-dimensional characteristic-zero association. 16/20; DUB-17--20 OPEN; all twenty acceptance gates unchanged.'
status = 'The nineteen-module scope passes 42 public axiom queries, 108 exhaustive scratch theorem checks, sixteen linters per module and three declaration-value audits with 60 required dependency checks, with zero diagnostics. Production aggregate, focused audits and sequential foundation/paper verification of the 9,026-module scope are pending.'
route = 'Reuse checks selected the existing ring-valued homogeneous monomial formula, original Picard arithmetic commutation, native Tate endomorphism map and Mathlib lcomp with the correct contragredient inverse. Native trace base change and the original subgroup H1 isomorphism give diamond invariance; the already used group/coefficient composition square avoids large cocycle unfolding. The existing prime-word transfer and original finite-character descent extend directly to actual diamonds. No new cohomology framework, broader-degree generalization, proof-limit change or external dependency is introduced. The separate optional Galois word wrapper remains unpromoted; the required prime-generator compatibility is proved. All promoted mathematical bodies remain identical to the scratch-audited bodies after import qualification.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Original Frobenius normalization, transfer and diamond-one character (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 9,007-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
corrections = []
count = sum(z['exhaustiveTheorems'] for z in certs)
assert count == 108

docpaths = list(dict.fromkeys(r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]))
for f in docpaths:
    assert "\n\n" in f.read_text(encoding="utf-8")
readmes = [(r.parent / "README.md", "Current Project 83 status ("), (repo / "README.md", "Project 83 has an ")]
for f, prefix in readmes:
    assert sum(line.startswith(prefix) for line in f.read_text(encoding="utf-8").splitlines()) == 1
arch = r / "Dubon Architecture.md"
edge = '  ARITHDIAM9007["Original arithmetic field/Picard/period/Tate diamonds, Galois commutation, exact homogeneous normalizer coefficient action and native finite H1 comparison proved. Parabolic transfer preimages, exceptional primes, Frobenius/inertia, characteristic-zero association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourceFrobeniusDiamondProductionAudit9026.lean',p/'source-frobenius-diamond-9026-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production9026.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/arithmetic-diamond-comparison-20261028-1241'
registered = {row['path'] for row in c['files']}
for priorFile in priorArchive.iterdir():
    rel = priorFile.relative_to(r).as_posix()
    if priorFile.is_file() and rel not in registered:
        c['files'].append({'path': rel, 'role': 'Tools'})

reportSource = p / 'Dubon Frobenius Normalization and Diamond Character Assessment 2026-10-28.md'
assert sha(reportSource) == 'EE0EBEE9E8DC40C90B0D9ECA50435E8B4E06C3F23D51BE33E29749A8559C517B'
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
    "productionModules": 9026, "modules": newmods, "queries": queries,
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
arch.write_text(arch.read_text(encoding='utf-8').replace(edge,'  ARITHDIAM9007["Original arithmetic field/Picard/period/Tate diamonds, Galois commutation and exact homogeneous normalizer coefficients proved (DUB-17/18)"] --> FROBDIAM9026\n  FROBDIAM9026["Exact conditional Frobenius normalization; ambient Galois/Hecke compatibility; native diamond transfer invariance and original full-H1 diamond-one finite character proved. Geometric Frobenius/inertia, parabolic realization, characteristic-zero association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'),encoding='utf-8')



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Original Frobenius normalization, transfer and diamond-one character - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-frobenius-diamond.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub('  logInfo m!".*"\\n', '  logInfo m!"SOURCE FROBENIUS DIAMOND AUDIT PASS: {count} theorems including private/generated declarations. Exact conditional Frobenius normalization, original Galois/Hecke compatibility, native transfer invariance and full-H1 diamond-one character. Geometric Frobenius/inertia, parabolic and characteristic-zero realization remain;16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourceFrobeniusDiamondProductionAudit9026.lean").write_text(out, encoding="utf-8")
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
    target = p / (source.stem + "Production9026.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
(p / "source-frobenius-diamond-9026-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 9026, "increment": 19, "queries": 42,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
