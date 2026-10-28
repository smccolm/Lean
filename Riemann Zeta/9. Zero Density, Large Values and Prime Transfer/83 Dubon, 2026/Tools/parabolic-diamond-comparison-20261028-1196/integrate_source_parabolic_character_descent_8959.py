from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 8947
assert d["appliedSourceGammaOneHomogeneousParabolic"]["receipt8947"]["exit"] == 0
assert (p / "paper-verification-8947-console.exit").read_text().strip() == "0"
assert (r/'Tools/gamma-one-homogeneous-parabolic-20261028-1163/canonical-evidence-8947.json').exists()
key = "appliedSourceParabolicCharacterDescent"
assert key not in d
digests = {'source-primitive-parabolic-kernel-1-scratch-receipt.json': '69482259BBA89FFC7FFAC9E9D3EB3B771469D0AFBF5FC1FC0D973FC79C1915FD', 'source-integral-saturation-1-scratch-receipt.json': 'F4214A6C467BADE0561B38AE8BA313083A1A24BA0369EA7BB80170F593232F65', 'source-supported-parabolic-congruence-1b-scratch-receipt.json': '32E039C33E09CAA84BBA6CD4500ACADCD1D357D2E98561721A2AC0634169E05D', 'source-gamma-one-parabolic-descent-1-scratch-receipt.json': 'E87AAD117C5DEFAD469542924BC56860E53CDCA1300079CAE42A0FCA19C0E298'}

for name, digest in digests.items():
    assert sha(p / name) == digest
certs = [json.loads((p / name).read_text(encoding="utf-8")) for name in digests]
mods = [m for z in certs for m in z["modules"]]
queries = [q for z in certs for q in z["queries"]]
theorems = [q for z in certs for q in z["theoremRegistrations"]]
defs = [q for z in certs for q in z["constructionRegistrations"]]
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (12, 12, 24, 19, 5)
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
archive_rel='Tools/parabolic-character-descent-20261028-1183'
evidence=[p/'parabolic-character-descent-promotion-route-1183.json']
evidence += [p/n for n in ['SourceFiniteIntegralSaturation.lean', 'SourceFiniteIntegralSaturation1167a.exit', 'SourceFiniteIntegralSaturation1167a.log', 'SourceFiniteIntegralSaturation1167b.exit', 'SourceFiniteIntegralSaturation1167b.log', 'SourceFiniteIntegralSaturation1167c.exit', 'SourceFiniteIntegralSaturation1167c.log', 'SourceFiniteIntegralSaturation1167d.exit', 'SourceFiniteIntegralSaturation1167d.log', 'SourceFiniteIntegralSaturation1167e.exit', 'SourceFiniteIntegralSaturation1167e.log', 'SourceGammaOneParabolicCharacterTransfer.lean', 'SourceGammaOneParabolicCharacterTransfer1178a.exit', 'SourceGammaOneParabolicCharacterTransfer1178a.log', 'SourceGammaOneParabolicCharacterTransfer1178b.exit', 'SourceGammaOneParabolicCharacterTransfer1178b.log', 'SourceGammaOneParabolicCharacterTransfer1178c.exit', 'SourceGammaOneParabolicCharacterTransfer1178c.log', 'SourceGammaOneParabolicCharacterTransfer1178d.exit', 'SourceGammaOneParabolicCharacterTransfer1178d.log', 'SourceGammaOneParabolicDescentAudit1.exit', 'SourceGammaOneParabolicDescentAudit1.lean', 'SourceGammaOneParabolicDescentAudit1.log', 'SourceGammaOneParabolicDescentDependencyAudit1.exit', 'SourceGammaOneParabolicDescentDependencyAudit1.lean', 'SourceGammaOneParabolicDescentDependencyAudit1.log', 'SourceGammaOneParabolicDescentScratchOwnership1181.exit', 'SourceGammaOneParabolicDescentScratchOwnership1181.lean', 'SourceGammaOneParabolicDescentScratchOwnership1181.log', 'SourceGammaOneParabolicOperatorAlgebra.lean', 'SourceGammaOneParabolicOperatorAlgebra1176a.exit', 'SourceGammaOneParabolicOperatorAlgebra1176a.log', 'SourceGammaOneParabolicTateKernel.lean', 'SourceGammaOneParabolicTateKernel1177a.exit', 'SourceGammaOneParabolicTateKernel1177a.log', 'SourceGammaOneParabolicTateKernel1177b.exit', 'SourceGammaOneParabolicTateKernel1177b.log', 'SourceGammaOneParabolicTateKernel1177c.exit', 'SourceGammaOneParabolicTateKernel1177c.log', 'SourceGammaOneParabolicTateKernel1177d.exit', 'SourceGammaOneParabolicTateKernel1177d.log', 'SourceGammaOneParabolicTransferCriterion.lean', 'SourceGammaOneParabolicTransferCriterion1179a.exit', 'SourceGammaOneParabolicTransferCriterion1179a.log', 'SourceGammaOneParabolicTransferCriterion1179b.exit', 'SourceGammaOneParabolicTransferCriterion1179b.log', 'SourceIntegralSaturationAudit1.exit', 'SourceIntegralSaturationAudit1.lean', 'SourceIntegralSaturationAudit1.log', 'SourceIntegralSaturationDependencyAudit1.exit', 'SourceIntegralSaturationDependencyAudit1.lean', 'SourceIntegralSaturationDependencyAudit1.log', 'SourceIntegralSaturationScratchOwnership1183.exit', 'SourceIntegralSaturationScratchOwnership1183.lean', 'SourceIntegralSaturationScratchOwnership1183.log', 'SourceParabolicAdicOperatorKernel.lean', 'SourceParabolicAdicOperatorKernel1174a.exit', 'SourceParabolicAdicOperatorKernel1174a.log', 'SourceParabolicAdicOperatorKernel1174b.exit', 'SourceParabolicAdicOperatorKernel1174b.log', 'SourceParabolicCongruenceException.lean', 'SourceParabolicCongruenceException1180a.exit', 'SourceParabolicCongruenceException1180a.log', 'SourceParabolicHeckeCongruence.lean', 'SourceParabolicHeckeCongruence1173a.exit', 'SourceParabolicHeckeCongruence1173a.log', 'SourceParabolicHeckeCongruence1173b.exit', 'SourceParabolicHeckeCongruence1173b.log', 'SourceParabolicHeckeCongruence1173c.exit', 'SourceParabolicHeckeCongruence1173c.log', 'SourceParabolicHeckeCongruence1173d.exit', 'SourceParabolicHeckeCongruence1173d.log', 'SourceParabolicHeckeSpan.lean', 'SourceParabolicHeckeSpan1172a.exit', 'SourceParabolicHeckeSpan1172a.log', 'SourceParabolicHeckeSpan1172b.exit', 'SourceParabolicHeckeSpan1172b.log', 'SourceParabolicHeckeSpan1172c.exit', 'SourceParabolicHeckeSpan1172c.log', 'SourceParabolicHeckeSpan1172d.exit', 'SourceParabolicHeckeSpan1172d.log', 'SourceParabolicHeckeSpan1172e.exit', 'SourceParabolicHeckeSpan1172e.log', 'SourceParabolicHeckeSpan1172f.exit', 'SourceParabolicHeckeSpan1172f.log', 'SourceParabolicReductionKernel.lean', 'SourceParabolicReductionKernel1168a.exit', 'SourceParabolicReductionKernel1168a.log', 'SourceParabolicReductionKernelAudit1.exit', 'SourceParabolicReductionKernelAudit1.lean', 'SourceParabolicReductionKernelAudit1.log', 'SourceParabolicReductionKernelDependencyAudit1.exit', 'SourceParabolicReductionKernelDependencyAudit1.lean', 'SourceParabolicReductionKernelDependencyAudit1.log', 'SourceParabolicReductionKernelDependencyAudit1b.exit', 'SourceParabolicReductionKernelDependencyAudit1b.lean', 'SourceParabolicReductionKernelDependencyAudit1b.log', 'SourceParabolicReductionKernelScratchOwnership1169.exit', 'SourceParabolicReductionKernelScratchOwnership1169.lean', 'SourceParabolicReductionKernelScratchOwnership1169.log', 'SourcePrimitiveParabolicCharacterKernel.lean', 'SourcePrimitiveParabolicCharacterKernel1165a.exit', 'SourcePrimitiveParabolicCharacterKernel1165a.log', 'SourcePrimitiveParabolicCharacterKernel1165b.exit', 'SourcePrimitiveParabolicCharacterKernel1165b.log', 'SourcePrimitiveParabolicKernelAudit1.exit', 'SourcePrimitiveParabolicKernelAudit1.lean', 'SourcePrimitiveParabolicKernelAudit1.log', 'SourcePrimitiveParabolicKernelDependencyAudit1.exit', 'SourcePrimitiveParabolicKernelDependencyAudit1.lean', 'SourcePrimitiveParabolicKernelDependencyAudit1.log', 'SourcePrimitiveParabolicKernelScratchOwnership1166.exit', 'SourcePrimitiveParabolicKernelScratchOwnership1166.lean', 'SourcePrimitiveParabolicKernelScratchOwnership1166.log', 'SourceSupportedCharacterDivisibility.lean', 'SourceSupportedCharacterDivisibility1171a.exit', 'SourceSupportedCharacterDivisibility1171a.log', 'SourceSupportedCharacterFiber.lean', 'SourceSupportedCharacterFiber1170a.exit', 'SourceSupportedCharacterFiber1170a.log', 'SourceSupportedCharacterFiber1170b.exit', 'SourceSupportedCharacterFiber1170b.log', 'SourceSupportedParabolicCongruenceAudit1b.exit', 'SourceSupportedParabolicCongruenceAudit1b.lean', 'SourceSupportedParabolicCongruenceAudit1b.log', 'SourceSupportedParabolicCongruenceDependencyAudit1b.exit', 'SourceSupportedParabolicCongruenceDependencyAudit1b.lean', 'SourceSupportedParabolicCongruenceDependencyAudit1b.log', 'SourceSupportedParabolicCongruenceScratchOwnership1175.lean', 'SourceSupportedParabolicCongruenceScratchOwnership1175b.exit', 'SourceSupportedParabolicCongruenceScratchOwnership1175b.lean', 'SourceSupportedParabolicCongruenceScratchOwnership1175b.log', 'audit_gamma_one_parabolic_descent_1181.ps1', 'audit_integral_saturation_1183.ps1', 'audit_parabolic_character_kernel_1166.ps1', 'audit_parabolic_reduction_kernel_1169.ps1', 'audit_parabolic_reduction_kernel_1169b.ps1', 'audit_supported_parabolic_congruence_1175.ps1', 'audit_supported_parabolic_congruence_1175b.ps1', 'compile_parabolic_transfer_repair_1179b.ps1', 'compile_supported_parabolic_doc_repair_1175b.ps1', 'consumers1170-focus.log', 'consumers1170.txt', 'consumers1177-focus.log', 'consumers1177.txt', 'docs1170.py', 'docs1177.py', 'factor1166-focus.log', 'factor1166b-focus.log', 'factor1166c-focus.log', 'factor1166d-focus.log', 'factor1167-focus.log', 'factor1168-focus.log', 'factor1168b-focus.log', 'factor1169-focus.log', 'factor1170-focus.log', 'fetch_parabolic_shapiro_candidates_1182.py', 'foundation1170-console.log', 'foundation1177-console.log', 'modules1170.json', 'modules1177.json', 'next1170-counts.json', 'paper1170-console.log', 'paper1177-console.log', 'parabolic-character-descent-promotion-route-1183.json', 'prepare_gamma_one_parabolic_descent_audit_1181.py', 'prepare_integral_saturation_scope_1183.py', 'prepare_parabolic_character_kernel_audit_1166.py', 'prepare_parabolic_reduction_audit_1169.py', 'prepare_parabolic_reduction_scope_repair_1169b.py', 'prepare_primitive_parabolic_kernel_audit_1166.py', 'prepare_supported_character_division_1171.py', 'prepare_supported_character_route_1170.py', 'prepare_supported_parabolic_audit_1175.py', 'prepare_supported_parabolic_audit_1175b.py', 'prepare_supported_parabolic_audit_repair_1175b.py', 'record1170.py', 'record1177.py', 'record_gamma_one_parabolic_descent_1181.py', 'record_integral_saturation_1183.py', 'record_parabolic_character_kernel_1166.py', 'record_parabolic_operator_route_1176.py', 'record_parabolic_reduction_kernel_1169.py', 'record_parabolic_reduction_kernel_1169b.py', 'record_supported_parabolic_congruence_1175.py', 'record_supported_parabolic_congruence_1175b.py', 'register1170.py', 'register1177.py', 'registrations1170.json', 'registrations1177.json', 'section1170.txt', 'section1177.txt', 'source-gamma-one-parabolic-descent-1-audit-config.json', 'source-gamma-one-parabolic-descent-1-reuse-review-20261028.json', 'source-gamma-one-parabolic-descent-1-scratch-receipt.json', 'source-gamma-one-parabolic-descent-audit-route-1181.json', 'source-integral-saturation-1-audit-config.json', 'source-integral-saturation-1-reuse-review-20261028.json', 'source-integral-saturation-1-scratch-receipt.json', 'source-integral-saturation-audit-route-1183.json', 'source-parabolic-operator-reuse-1176.json', 'source-parabolic-reduction-kernel-1-audit-config.json', 'source-parabolic-reduction-kernel-1-reuse-review-20261028.json', 'source-parabolic-reduction-kernel-1-scratch-receipt.json', 'source-parabolic-reduction-kernel-1b-reuse-review-20261028.json', 'source-parabolic-reduction-kernel-1b-scratch-receipt.json', 'source-parabolic-reduction-kernel-audit-route-1169.json', 'source-parabolic-saturation-reuse-1167.json', 'source-primitive-parabolic-kernel-1-audit-config.json', 'source-primitive-parabolic-kernel-1-reuse-review-20261028.json', 'source-primitive-parabolic-kernel-1-scratch-receipt.json', 'source-primitive-parabolic-kernel-audit-route-1166.json', 'source-primitive-parabolic-relation-1-scratch-receipt.json', 'source-supported-character-reuse-1170.json', 'source-supported-parabolic-congruence-1b-audit-config.json', 'source-supported-parabolic-congruence-1b-reuse-review-20261028.json', 'source-supported-parabolic-congruence-1b-scratch-receipt.json', 'source-supported-parabolic-congruence-audit-route-1175.json', 'source-supported-parabolic-congruence-audit-route-1175b.json', 'status1170.txt', 'status1177.txt']]
for folder in ['finite-integral-saturation-1167a', 'finite-integral-saturation-1167b', 'finite-integral-saturation-1167c', 'finite-integral-saturation-1167d', 'parabolic-character-transfer-1178a', 'parabolic-character-transfer-1178b', 'parabolic-character-transfer-1178c', 'parabolic-hecke-congruence-1173a', 'parabolic-hecke-congruence-1173b', 'parabolic-hecke-span-1172a', 'parabolic-hecke-span-1172b', 'parabolic-hecke-span-1172c', 'parabolic-hecke-span-1172d', 'parabolic-shapiro-reuse-1182', 'parabolic-tate-kernel-1177a', 'parabolic-tate-kernel-1177b', 'parabolic-tate-kernel-1177c', 'parabolic-transfer-criterion-1179a', 'primitive-parabolic-character-kernel-1165a', 'supported-parabolic-audit-1175a']:
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
supplemental_review_path=r/archive_rel/'parabolic-character-descent-promotion-route-1183.json'

audit = r / "Extension/Dubon2026/Audit.lean"
at = audit.read_text(encoding="utf-8")
for n in queries:
    assert not re.search(r"``" + re.escape(n) + r"(?=[,\s])", at)
tm, dm = "\n]\n\nprivate def publicConstructions", "\n]\n\nprivate def runAudit"
assert at.count(tm) == at.count(dm) == 1
at = at.replace(tm, "".join("\n  ,``" + n for n in theorems) + tm, 1)
at = at.replace(dm, "".join("\n  ," + chr(96)*2 + n for n in defs) + dm, 1)
research_path = r / "Tools/lean-reuse-audit-20261020.json"
reuse_path = r / "Tools/source-parabolic-character-descent.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt8947"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> arithmetic realization of original finite Gamma1 homogeneous-coefficient Hecke characters -> finite parabolic character descent -> original character support, integral Hecke-span saturation, actual parabolic operator congruence and exact geometric transfer preimages.'
discharged = 'The already constructed original complex and Fourier-field H1 characters annihilate every operator zero on original integral parabolic H1. The actual integral Hecke span of those classes is finite and supports the same original character. Native finite-module support, a nonzero character fiber and a fixed torsion annihilator prove integrality of the original character value divided by every nonzero modulus coprime to one fixed nonzero integer when the operator vanishes after reduction on integral parabolic H1. Consequently the same compatible adic character kills such operators at every positive power of every prime away from that integer, uniformly in field and embedding. The literal finite Gamma1 parabolic operator ring is finite. Its zero-word relations equal those of the independently defined arithmetic Picard Tate-dual action. Assuming explicitly that each reduced original integral parabolic class has a parabolic preimage under the existing native transfer, the same whole original adic character descends to that actual finite operator ring.'
boundary = 'The geometric lifting condition sourceGammaOneIntegralParabolicTransfer is stated and remains unproved. The finite-character descent theorem is conditional on that precise transfer input and excludes the primes dividing the proved fixed nonzero integer. Neither full-H1 transfer surjectivity nor restriction landing in parabolic H1 discharges it. The already proved all-prime full-H1 character family remains unchanged. Exceptional primes, diamonds, coefficient-field/Frobenius/inertia realization, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain. Finite characters do not supply a characteristic-zero lift.16/20; DUB-17--20 OPEN; all twenty acceptance gates unchanged.'
status = 'The twelve-module original parabolic congruence and conditional finite Gamma1 descent scope passes 24 public axiom queries, 35 exhaustive scratch theorem checks, sixteen linters per module and four declaration-value audits with 55 required dependency checks, with zero diagnostics. Production aggregate, focused audits and sequential foundation/paper verification of the 8,959-module scope are pending.'
route = 'Reuse the October 28 nine-repository refresh and the targeted public parabolic-Shapiro/finite-field comparison check. Native support, finite torsion annihilators, the existing original Fourier-character kernel and Hecke-word maps give the shorter integral Hecke-span route. It avoids general integral parabolic corestriction stability, a new unipotent cokernel classification, and a transient finite tensor algebra on that span. The separately audited direct parabolic reduction-kernel theorem is deferred as unnecessary for this route. The public complex-coefficient Shapiro entry displays a statement, not its accepted proof body, and does not prove the finite-coefficient counit lifting required here. Frozen mathematical bodies are promoted by import qualification only.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Original parabolic operator congruence and conditional finite Gamma1 character descent (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 8,947-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
corrections = []
count = sum(z['exhaustiveTheorems'] for z in certs)
assert count == 35

docpaths = list(dict.fromkeys(r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]))
for f in docpaths:
    assert "\n\n" in f.read_text(encoding="utf-8")
readmes = [(r.parent / "README.md", "Current Project 83 status ("), (repo / "README.md", "Project 83 has an ")]
for f, prefix in readmes:
    assert sum(line.startswith(prefix) for line in f.read_text(encoding="utf-8").splitlines()) == 1
arch = r / "Dubon Architecture.md"
edge = '  GAMMAONEHOMOGPARAB8947["Original homogeneous arithmetic Tate dual/parabolic H1 and whole Hecke words proved; original nonzero parabolic eigenclass, integral span and integral operator relations proved. Finite character descent, diamonds, Galois realization and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourceParabolicCharacterDescentProductionAudit8959.lean',p/'source-parabolic-character-descent-8959-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production8959.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/gamma-one-homogeneous-parabolic-20261028-1163'
registered = {row['path'] for row in c['files']}
for priorFile in priorArchive.iterdir():
    rel = priorFile.relative_to(r).as_posix()
    if priorFile.is_file() and rel not in registered:
        c['files'].append({'path': rel, 'role': 'Tools'})

reportSource = p / 'Dubon Parabolic Character Descent Reuse Assessment 2026-10-28.md'
assert sha(reportSource) == '120E8C94055BA937F920071CE6B7AEF68689550EB973B379D4BB9365DFB08417'
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
    "productionModules": 8959, "modules": newmods, "queries": queries,
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
arch.write_text(arch.read_text(encoding='utf-8').replace(edge,'  GAMMAONEHOMOGPARAB8947["Original homogeneous arithmetic Tate dual/parabolic H1, whole Hecke words, nonzero original parabolic eigenclass and integral span proved (DUB-17/18)"] --> PARABCHAR8959\n  PARABCHAR8959["Original parabolic operator congruences at all precisions away from one fixed integer proved; actual finite parabolic/Tate word kernels identified. Character descent CONDITIONAL on exact parabolic transfer preimages. Exceptions, diamonds, Galois realization and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'),encoding='utf-8')



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Original parabolic operator congruence and conditional finite Gamma1 character descent - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-parabolic-character-descent.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub('  logInfo m!".*"\\n', '  logInfo m!"SOURCE PARABOLIC CHARACTER DESCENT AUDIT PASS: {count} theorems including private/generated declarations. Original parabolic congruence away from a fixed integer, actual finite parabolic/Tate word kernel, and explicitly conditional transfer descent. Geometric lifting, exceptional primes, diamonds and all-weight association remain;16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourceParabolicCharacterDescentProductionAudit8959.lean").write_text(out, encoding="utf-8")
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
    target = p / (source.stem + "Production8959.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
(p / "source-parabolic-character-descent-8959-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 8959, "increment": 12, "queries": 24,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
