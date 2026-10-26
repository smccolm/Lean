from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 8213
assert d["appliedSourcePrimitiveWittDeformation"]["receipt8213"]["exit"] == 0
assert (p / "paper-verification-8213-console.exit").read_text().strip() == "0"
key = "appliedSourcePrimitiveFiniteH1Realization"
assert key not in d
digests = {'source-binary-prime-power-permutation-5-scratch-receipt.json': '131D80CB8B20E3D334985ED27E816A49B87EB125EBBF4CCA662AEDD7E6582C04', 'source-primitive-h1-adic-5-scratch-receipt.json': '35507B2755D1A2A461D5D487913AA2CC6A66FB0F8003002F7A09AB1D66310A36', 'source-binary-stabilizer-h1-3-scratch-receipt.json': '0F2EF92CDA71B594734C0C2964B97A7888203148B19F72584FC0627391719161', 'source-primitive-h1-congruence-5-scratch-receipt.json': '410DDC92612FC3D1680315BA92F65C0DC97D6F813A76891371BB54F162452ADF', 'source-primitive-finite-operator-character-4-scratch-receipt.json': 'D8986017528A0357284AE33F6112282F474A767948B3D6FAFE2C81A52A29913E', 'source-primitive-permutation-operator-character-7-scratch-receipt.json': '1521C47DC2376E468B567A6A71369D059C12D1EF97A27B69BE43FFC87A53D0B3'}

for name, digest in digests.items():
    assert sha(p / name) == digest
certs = [json.loads((p / name).read_text(encoding="utf-8")) for name in digests]
mods = [m for z in certs for m in z["modules"]]
queries = [q for z in certs for q in z["queries"]]
theorems = [q for z in certs for q in z["theoremRegistrations"]]
defs = [q for z in certs for q in z["constructionRegistrations"]]
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (29, 29, 76, 53, 23)
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
archive_rel='Tools/primitive-finite-permutation-h1-20261025-590'
evidence=[p/'primitive-finite-permutation-h1-promotion-route-590.json']

evidence += [p/name for name in digests]
evidence += [p/name for name in ['SourceBinaryPrimePowerPermutationAudit5.exit', 'SourceBinaryPrimePowerPermutationAudit5.lean', 'SourceBinaryPrimePowerPermutationAudit5.log', 'SourceBinaryPrimePowerPermutationDependencyAudit5.exit', 'SourceBinaryPrimePowerPermutationDependencyAudit5.lean', 'SourceBinaryPrimePowerPermutationDependencyAudit5.log', 'SourceBinaryStabilizerH1Audit3.exit', 'SourceBinaryStabilizerH1Audit3.lean', 'SourceBinaryStabilizerH1Audit3.log', 'SourceBinaryStabilizerH1DependencyAudit3.exit', 'SourceBinaryStabilizerH1DependencyAudit3.lean', 'SourceBinaryStabilizerH1DependencyAudit3.log', 'SourcePrimitiveFiniteOperatorCharacterAudit4.exit', 'SourcePrimitiveFiniteOperatorCharacterAudit4.lean', 'SourcePrimitiveFiniteOperatorCharacterAudit4.log', 'SourcePrimitiveFiniteOperatorCharacterDependencyAudit4.exit', 'SourcePrimitiveFiniteOperatorCharacterDependencyAudit4.lean', 'SourcePrimitiveFiniteOperatorCharacterDependencyAudit4.log', 'SourcePrimitiveH1AdicAudit5.exit', 'SourcePrimitiveH1AdicAudit5.lean', 'SourcePrimitiveH1AdicAudit5.log', 'SourcePrimitiveH1AdicDependencyAudit5.exit', 'SourcePrimitiveH1AdicDependencyAudit5.lean', 'SourcePrimitiveH1AdicDependencyAudit5.log', 'SourcePrimitiveH1AdicDependencyAudit5b.exit', 'SourcePrimitiveH1AdicDependencyAudit5b.lean', 'SourcePrimitiveH1AdicDependencyAudit5b.log', 'SourcePrimitiveH1CongruenceAudit5.exit', 'SourcePrimitiveH1CongruenceAudit5.lean', 'SourcePrimitiveH1CongruenceAudit5.log', 'SourcePrimitiveH1CongruenceDependencyAudit5.exit', 'SourcePrimitiveH1CongruenceDependencyAudit5.lean', 'SourcePrimitiveH1CongruenceDependencyAudit5.log', 'binary-prime-power-permutation-route-582.json', 'binary-stabilizer-h1-route-584.json', 'prepare_binary_prime_power_permutation_audit_582.py', 'prepare_binary_stabilizer_h1_audit_584.py', 'prepare_primitive_finite_operator_character_audit_586.py', 'prepare_primitive_h1_adic_audit_583.py', 'prepare_primitive_h1_congruence_audit_585.py', 'primitive-finite-operator-character-route-586.json', 'primitive-h1-adic-route-583.json', 'primitive-h1-adic-route-583b.json', 'primitive-h1-adic-value-successor-583b.json', 'primitive-h1-congruence-route-585.json', 'record_binary_prime_power_permutation_582.py', 'record_binary_stabilizer_h1_584.py', 'record_primitive_finite_operator_character_586.py', 'record_primitive_h1_adic_583.py', 'record_primitive_h1_adic_583b.py', 'record_primitive_h1_congruence_585.py', 'source-binary-prime-power-permutation-5-audit-config.json', 'source-binary-stabilizer-h1-3-audit-config.json', 'source-primitive-finite-operator-character-4-audit-config.json', 'source-primitive-h1-adic-5-audit-config-583b.json', 'source-primitive-h1-adic-5-audit-config.json', 'source-primitive-h1-congruence-5-audit-config.json']]
evidence += [p/name for name in ['SourcePrimitivePermutationOperatorCharacterAudit7.exit', 'SourcePrimitivePermutationOperatorCharacterAudit7.lean', 'SourcePrimitivePermutationOperatorCharacterAudit7.log', 'SourcePrimitivePermutationOperatorCharacterDependencyAudit7.exit', 'SourcePrimitivePermutationOperatorCharacterDependencyAudit7.lean', 'SourcePrimitivePermutationOperatorCharacterDependencyAudit7.log', 'archive_primitive_finite_h1_canonical_8235.py', 'binary-permutation-operator-character-route-588.json', 'build_primitive_finite_h1_realization_8235.ps1', 'compare_primitive_finite_h1_realization_ownership_8235.py', 'integrate_source_primitive_finite_h1_realization_8235.py', 'prepare_primitive_finite_h1_promotion_8235.py', 'prepare_primitive_finite_h1_realization_global_ownership_8235.py', 'prepare_primitive_finite_h1_realization_production_ownership_8235.py', 'prepare_primitive_finite_h1_realization_scratch_ownership_8235.py', 'prepare_primitive_permutation_operator_character_audit_588.py', 'primitive-finite-h1-preexecution-review-8235.json', 'primitive-finite-h1-promotion-route-587.json', 'record_primitive_permutation_operator_character_588.py', 'record_source_primitive_finite_h1_realization_8235.py', 'source-primitive-permutation-operator-character-7-audit-config.json', 'verify_primitive_finite_h1_realization_8235.ps1']]
for folder in ['finite-operator-586-before-abstract-descent','finite-operator-586-before-explicit-descent-arguments']:
    evidence += sorted((p/folder).iterdir())
for cert in certs:
    evidence.append(Path(cert['reuseReview']))

for cert in certs:
    for field in ['log','dependencyAuditLog']:
        f=Path(cert[field]); evidence.extend([f,f.with_suffix('.lean'),f.with_suffix('.exit')])
archive=[]
for source in dict.fromkeys(evidence):
    assert source.exists(),source
    target=r/archive_rel/(source.parent.name if source.parent != p else '')/(source.name+('.txt' if source.suffix=='.lean' else ''))
    assert not target.exists(),target
    refresh_pending.append((target,source.read_bytes(),'Tools'))
    archive.append(dict(source=str(source),path=target.relative_to(r).as_posix(),sha256=sha(source)))
archive_target=r/archive_rel/'archive-manifest.json'
assert not archive_target.exists()
refresh_pending.append((archive_target,(json.dumps(dict(files=archive),indent=2)+'\n').encode(),'Tools'))
supplemental_review_path=r/archive_rel/'primitive-finite-permutation-h1-promotion-route-590.json'

audit = r / "Extension/Dubon2026/Audit.lean"
at = audit.read_text(encoding="utf-8")
for n in queries:
    assert not re.search(r"``" + re.escape(n) + r"(?=[,\s])", at)
tm, dm = "\n]\n\nprivate def publicConstructions", "\n]\n\nprivate def runAudit"
assert at.count(tm) == at.count(dm) == 1
at = at.replace(tm, "".join("\n  ,``" + n for n in theorems) + tm, 1)
at = at.replace(dm, "," + "".join("\n  ``" + n + ("," if i + 1 < len(defs) else "")
                                 for i, n in enumerate(defs)) + dm, 1)
research_path = r / "Tools/lean-reuse-audit-20261020.json"
reuse_path = r / "Tools/source-primitive-finite-h1-realization.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt8213"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero Galois association -> compatible geometric finite-precision Hecke realizations -> actual finite operator characters, original coefficient congruences and finite congruence-stabilizer H1 comparison -> canonical surjection from actual finite permutation Hecke operators to the original finite operator image'
discharged = 'For every original primitive form of weight at least two and every prescribed prime, the same original integral H1 Hecke character is valued in its literal Fourier coefficient field and actual local valuation ring. Its finite adic reductions are compatible as whole characters and have the exact original Fourier values. The nonzero faithful character fiber and native finite-lattice integrality prove that original operator congruences force matching character congruences. Every character therefore factors through the actual finite tensor-reduced H1 operator ring, with exact original pullback and prime values. Independently, at every positive power of every prime greater than three, the actual finite binary permutation coefficients map onto original H1 and retain all original prime Hecke transforms. Existing orbit, finite-product and Shapiro maps identify these permutation H1 groups with trivial-coefficient H1 of their actual finite-index congruence stabilizers. All coefficient-field, integrality, finite-residue, adic compatibility, character-kernel and cohomological comparison inputs in these consumers are derived. The full permutation H1 Hecke image is finite and canonically surjects onto the original finite tensor-operator image. Every relation is transferred using proved evaluation surjectivity, additive Hecke-word naturality and the exact original integral reduction kernel. Composing this surjection with the same original finite character gives permutation Hecke characters at every positive power of each prime greater than three, with whole-word pullback and exact original Fourier values. No relation or character-lifting premise is retained.'
boundary = 'The transported stabilizer operators have not yet been identified with arithmetic geometric correspondences. Geometric Galois realization of these finite characters, compatible characteristic-zero association, required local/image/regularity properties, arithmetic automorphy and literal higher symmetric-power continuation remain required. No eigenvector lift, arithmetic Galois action or characteristic-zero deformation point is claimed from the finite constructions alone. 16/20; DUB-17--20 OPEN.'
status = 'The original-form finite H1 and permutation Hecke-character chain passes 179 exhaustive scratch checks and 76 explicit axiom queries across 29 modules, with sixteen linters per module and zero diagnostics. Six declaration-value audits verify 124 required dependencies. Production aggregate, focused audit and sequential foundation/paper verification of the 8,242-module scope are pending.'
route = 'Reuse the existing integral H1 character, finite Hecke algebra, Fourier field and prescribed-prime completion; native quotient powers, finite-lattice integrality and tensor base change; the existing exact semilinear reduction kernel, faithful character fiber, finite permutation evaluation, Gamma0 H1 surjection, full Hecke naturality, orbit decomposition and Shapiro comparison. Explicit descent arguments avoid elaboration timeouts without changing hypotheses or proof limits. Native finite-index counit and new H2 torsion infrastructure are deferred because they are unnecessary for this route. The renewed primary-source search remains recorded; no external import or root pin change. The existing general additive Hecke-word intertwiner also gives the canonical permutation operator quotient; a new word-induction development and integral lifting of arbitrary residual H1 are unnecessary.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Actual original finite H1 characters and congruence realizations (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 8,213-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
corrections = []
count = sum(z['exhaustiveTheorems'] for z in certs)
assert count == 179

docpaths = list(dict.fromkeys(r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]))
for f in docpaths:
    assert "\n\n" in f.read_text(encoding="utf-8")
readmes = [(r.parent / "README.md", "Current Project 83 status ("), (repo / "README.md", "Project 83 has an ")]
for f, prefix in readmes:
    assert sum(line.startswith(prefix) for line in f.read_text(encoding="utf-8").splitlines()) == 1
arch = r / "Dubon Architecture.md"
edge = '  PRIMITIVEWITT8213["Global cyclotomic determinant, real oddness, finite residue field and actual complete Witt framed/fixed-determinant rings proved; original adic point, local/image/regularity and automorphy OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourcePrimitiveFiniteH1RealizationProductionAudit8242.lean',p/'source-primitive-finite-h1-realization-8242-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production8242.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/primitive-witt-20261025-581'
registered = {row['path'] for row in c['files']}
for priorFile in priorArchive.iterdir():
    rel = priorFile.relative_to(r).as_posix()
    if priorFile.is_file() and rel not in registered:
        c['files'].append({'path': rel, 'role': 'Tools'})

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
reuse['additionalCurrentSearch'] = dict(path=supplemental_review_path.relative_to(r).as_posix(),sha256=sha(supplemental_review_path))
reuse['renewedSourceArchive'] = dict(manifest=archive_target.relative_to(r).as_posix(),sha256=sha(archive_target),externalLocalBuild=False,externalImport=False)
reuse_path.write_text(json.dumps(reuse, indent=2) + "\n", encoding="utf-8")
c["files"].append({"path": reuse_path.relative_to(r).as_posix(), "role": "Tools"})
cp.write_text(json.dumps(c, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
d[key] = {"recordedUTC": datetime.now(timezone.utc).isoformat(), "date": dateLabel,
    "productionModules": 8242, "modules": newmods, "queries": queries,
    "theoremRegistrations": theorems, "constructionRegistrations": defs,
    "sourceHashes": {mapping[t.stem]: sha(t) for t, _ in pending}, "scratchCertificates": certs,
    "exactDependency": dependency, "assumptionsDischarged": discharged, "stillOpen": boundary,
    "status": status, "rootPinsChanged": False, "proofLimitsChanged": False,
    "promotionChanges": 'Only scratch imports are qualified. Every mathematical statement, proof body and module comment is preserved. The original primitive cusp form, Fourier coefficients, actual local fields, integral H1, Hecke operators, coefficient reductions and original finite permutation and stabilizer cohomology retain their definitions. No source contract is weakened.',
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
arch.write_text(arch.read_text(encoding='utf-8').replace(edge, '  PRIMITIVEWITT8213["Global cyclotomic determinant, real oddness, finite residue field and actual complete Witt framed/fixed-determinant rings (DUB-17/18)"] --> PRIMITIVEFINITEH18242\n  PRIMITIVEFINITEH18242["Compatible original finite H1 and permutation Hecke characters with a canonical surjection and congruence-stabilizer comparison proved; geometric Galois realization, adic association, local/image/regularity and automorphy OPEN (DUB-17/18)"] --> CMARITH4538'),encoding='utf-8')



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Actual original finite H1 characters and congruence realizations - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-primitive-finite-h1-realization.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub(r'  logInfo m!".*"\n',
    '  logInfo m!"SOURCE PRIMITIVE FINITE H1 REALIZATION AUDIT PASS: {count} theorems including private/generated declarations. The original all-weight form supplies compatible finite adic H1 characters on the actual finite operator image, with original Fourier values and operator-congruence compatibility. Original finite permutation H1 is identified with actual congruence-stabilizer H1 while retaining Hecke transforms. Geometric Galois realization, adic association, local/image/regularity, automorphy and higher continuation remain open; 16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourcePrimitiveFiniteH1RealizationProductionAudit8242.lean").write_text(out, encoding="utf-8")
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
    target = p / (source.stem + "Production8242.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
(p / "source-primitive-finite-h1-realization-8242-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 8242, "increment": 29, "queries": 76,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
