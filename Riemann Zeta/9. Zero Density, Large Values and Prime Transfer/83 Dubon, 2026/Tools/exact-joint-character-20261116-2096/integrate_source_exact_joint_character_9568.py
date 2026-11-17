from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 9559
assert d["appliedSourceOriginalGenusConsumers"]["receipt9559"]["exit"] == 0
assert (p / "paper-verification-9559-console.exit").read_text().strip() == "0"
assert (r/'Tools/original-genus-consumers-20261116-2037/canonical-evidence-9559.json').exists()
key = "appliedSourceExactJointCharacter"
assert key not in d
digests = {'source-gammaone-exact-joint-character-2-scratch-receipt.json': '29095882168BBDFAA253131A2F97076AF2182890B670E9FF4AF925C76F3DF89E'}

for name, digest in digests.items():
    assert sha(p / name) == digest
certs = [json.loads((p / name).read_text(encoding="utf-8")) for name in digests]
mods = [m for z in certs for m in z["modules"]]
queries = [q for z in certs for q in z["queries"]]
theorems = [q for z in certs for q in z["theoremRegistrations"]]
defs = [q for z in certs for q in z["constructionRegistrations"]]
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (9, 9, 18, 12, 6)
omitted = []
assert not set(mods).intersection(c["productionModules"])
mapping = {m: "Dubon2026." + m for m in c["productionModules"] + mods}
mapping["SourceGammaOneFiniteDivisorReciprocityAssembled"] = "Dubon2026.SourceGammaOneFiniteDivisorReciprocity"
# Qualify versioned imports from independently audited adjacent scratch scopes.
# Only a suffix naming a registered module is accepted; bodies/comments stay frozen.
for cert in certs:
    for item in cert['files']:
        for imported in re.findall(r'^import (\S+)',Path(item['path']).read_text(encoding='utf-8'),re.M):
            if imported in mapping or imported.startswith(('Dubon2026.','Mathlib.')):continue
            match=re.fullmatch(r'(Source.+?)([0-9]{4}[a-z]?)',imported)
            if match and match[1] in mods:mapping[imported]='Dubon2026.'+match[1]
for cert in certs:
    for source in [Path(cert['dependencyAuditLog']).with_suffix('.lean')] + [Path(x['path']) for x in cert['files']]:
        for imported in re.findall(r'\b(Source[A-Za-z0-9_]+)', source.read_text(encoding='utf-8')):
            match = re.fullmatch(r'(Source.+?)([0-9]{4}[a-z]?)', imported)
            if match and match[1] in mapping: mapping[imported] = mapping[match[1]]
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
archive_rel='Tools/exact-joint-character-20261116-2096'
evidence=[p/n for n in ['Dubon Exact Joint Character Assessment 2026-11-16.md', 'SourceGammaOneBoundaryQuotient-2095.exit', 'SourceGammaOneBoundaryQuotient-2095.log', 'SourceGammaOneBoundaryQuotient.lean', 'SourceGammaOneBoundaryQuotient2089a.exit', 'SourceGammaOneBoundaryQuotient2089a.lean.txt', 'SourceGammaOneBoundaryQuotient2089a.log', 'SourceGammaOneBoundaryQuotient2089b.exit', 'SourceGammaOneBoundaryQuotient2089b.lean.txt', 'SourceGammaOneBoundaryQuotient2089b.log', 'SourceGammaOneBoundaryQuotient2089c.exit', 'SourceGammaOneBoundaryQuotient2089c.lean', 'SourceGammaOneBoundaryQuotient2089c.log', 'SourceGammaOneBoundaryWordKernel-2043.exit', 'SourceGammaOneBoundaryWordKernel-2043.log', 'SourceGammaOneBoundaryWordKernel.lean', 'SourceGammaOneBoundaryWordKernel2040a.exit', 'SourceGammaOneBoundaryWordKernel2040a.lean.txt', 'SourceGammaOneBoundaryWordKernel2040a.log', 'SourceGammaOneBoundaryWordKernel2040b.exit', 'SourceGammaOneBoundaryWordKernel2040b.lean.txt', 'SourceGammaOneBoundaryWordKernel2040b.log', 'SourceGammaOneBoundaryWordKernel2040c.exit', 'SourceGammaOneBoundaryWordKernel2040c.lean', 'SourceGammaOneBoundaryWordKernel2040c.log', 'SourceGammaOneExactJointCharacter-2095.exit', 'SourceGammaOneExactJointCharacter-2095.log', 'SourceGammaOneExactJointCharacter-2100.exit', 'SourceGammaOneExactJointCharacter-2100.log', 'SourceGammaOneExactJointCharacter.lean', 'SourceGammaOneExactJointCharacter2092a.exit', 'SourceGammaOneExactJointCharacter2092a.lean', 'SourceGammaOneExactJointCharacter2092a.log', 'SourceGammaOneExactJointCharacterAudit1.exit', 'SourceGammaOneExactJointCharacterAudit1.lean.txt', 'SourceGammaOneExactJointCharacterAudit1.log', 'SourceGammaOneExactJointCharacterAudit2.exit', 'SourceGammaOneExactJointCharacterAudit2.lean', 'SourceGammaOneExactJointCharacterAudit2.log', 'SourceGammaOneExactJointCharacterDependencyAudit1.lean', 'SourceGammaOneExactJointCharacterDependencyAudit2.exit', 'SourceGammaOneExactJointCharacterDependencyAudit2.lean', 'SourceGammaOneExactJointCharacterDependencyAudit2.log', 'SourceGammaOneExactJointCharacterScratchOwnership2095.lean', 'SourceGammaOneExactJointCharacterScratchOwnership2100.exit', 'SourceGammaOneExactJointCharacterScratchOwnership2100.lean', 'SourceGammaOneExactJointCharacterScratchOwnership2100.log', 'SourceGammaOneExactJointFinite-2095.exit', 'SourceGammaOneExactJointFinite-2095.log', 'SourceGammaOneExactJointFinite-2100.exit', 'SourceGammaOneExactJointFinite-2100.log', 'SourceGammaOneExactJointFinite.lean', 'SourceGammaOneExactJointFinite2094a.exit', 'SourceGammaOneExactJointFinite2094a.lean.txt', 'SourceGammaOneExactJointFinite2094a.log', 'SourceGammaOneExactJointFinite2094b.exit', 'SourceGammaOneExactJointFinite2094b.lean', 'SourceGammaOneExactJointFinite2094b.log', 'SourceGammaOneExactJointFinite2094c.exit', 'SourceGammaOneExactJointFinite2094c.lean', 'SourceGammaOneExactJointFinite2094c.log', 'SourceGammaOneExactJointRing-2095.exit', 'SourceGammaOneExactJointRing-2095.log', 'SourceGammaOneExactJointRing-2100.exit', 'SourceGammaOneExactJointRing-2100.log', 'SourceGammaOneExactJointRing.lean', 'SourceGammaOneExactJointRing2090a.exit', 'SourceGammaOneExactJointRing2090a.lean', 'SourceGammaOneExactJointRing2090a.log', 'SourceGammaOneExactJointRing2090b.lean', 'SourceGammaOneExactJointRing2095Failed.lean.txt', 'SourceGammaOneExactJointSquare-2095.exit', 'SourceGammaOneExactJointSquare-2095.log', 'SourceGammaOneExactJointSquare-2100.exit', 'SourceGammaOneExactJointSquare-2100.log', 'SourceGammaOneExactJointSquare.lean', 'SourceGammaOneExactJointSquare2091a.exit', 'SourceGammaOneExactJointSquare2091a.lean', 'SourceGammaOneExactJointSquare2091a.log', 'SourceGammaOneGeometricExactJointCharacter-2095.exit', 'SourceGammaOneGeometricExactJointCharacter-2095.log', 'SourceGammaOneGeometricExactJointCharacter-2100.exit', 'SourceGammaOneGeometricExactJointCharacter-2100.log', 'SourceGammaOneGeometricExactJointCharacter.lean', 'SourceGammaOneGeometricExactJointCharacter2093a.exit', 'SourceGammaOneGeometricExactJointCharacter2093a.lean.txt', 'SourceGammaOneGeometricExactJointCharacter2093a.log', 'SourceGammaOneGeometricExactJointCharacter2093b.exit', 'SourceGammaOneGeometricExactJointCharacter2093b.lean.txt', 'SourceGammaOneGeometricExactJointCharacter2093b.log', 'SourceGammaOneGeometricExactJointCharacter2093c.exit', 'SourceGammaOneGeometricExactJointCharacter2093c.lean', 'SourceGammaOneGeometricExactJointCharacter2093c.log', 'SourceGammaOneJointOperatorRing2088a.exit', 'SourceGammaOneJointOperatorRing2088a.lean.txt', 'SourceGammaOneJointOperatorRing2088a.log', 'SourceGammaOneJointOperatorRing2088b.exit', 'SourceGammaOneJointOperatorRing2088b.lean', 'SourceGammaOneJointOperatorRing2088b.log', 'SourceOperatorRangeCharacter-2095.exit', 'SourceOperatorRangeCharacter-2095.log', 'SourceOperatorRangeCharacter.lean', 'SourceOperatorRangeCharacter2086a.exit', 'SourceOperatorRangeCharacter2086a.lean', 'SourceOperatorRangeCharacter2086a.log', 'SourcePrimitiveH1SquareCongruence-2095.exit', 'SourcePrimitiveH1SquareCongruence-2095.log', 'SourcePrimitiveH1SquareCongruence.lean', 'SourcePrimitiveH1SquareCongruence2080a.exit', 'SourcePrimitiveH1SquareCongruence2080a.lean', 'SourcePrimitiveH1SquareCongruence2080a.log', 'audit_gammaone_exact_joint_character_2095.ps1', 'audit_gammaone_exact_joint_character_2100.ps1', 'build_gammaone_exact_joint_character_canonical_2095.ps1', 'build_gammaone_exact_joint_character_canonical_2100.ps1', 'exact-joint-character-promotion-route-2096.json', 'expanded-reuse-20261116-2071/expanded-reuse-assessment-2079.md.txt', 'expanded-reuse-20261116-2071/publication-manifest-2079.json', 'gammaone-exact-joint-character-versions-2095.json', 'prepare_exact_joint_character_audit_2095.py', 'record_gammaone_exact_joint_character_2095.py', 'record_gammaone_exact_joint_character_2100.py', 'repair_exact_joint_character_linter_2100.py', 'source-gammaone-exact-joint-character-1-audit-config.json', 'source-gammaone-exact-joint-character-2-audit-config.json', 'source-gammaone-exact-joint-character-2-reuse-review-20261116.json', 'source-gammaone-exact-joint-character-2-scratch-receipt.json', 'source-gammaone-exact-joint-character-audit-route-2095.json', 'source-gammaone-exact-joint-character-audit-route-2100.json']]
for cert in certs:
    evidence.append(Path(cert['reuseReview']))

for cert in certs:
    for field in ['log','dependencyAuditLog']:
        f=Path(cert[field]); evidence.extend([f,f.with_suffix('.lean'),f.with_suffix('.exit')])
archive=[]
archiveBytes={}
for source in dict.fromkeys(evidence):
    assert source.exists(),source
    target=r/archive_rel/source.relative_to(p)
    if source.suffix in ['.lean','.md']:target=target.with_name(target.name+'.txt')
    assert not target.exists(),target
    data=source.read_bytes()
    if target in archiveBytes and archiveBytes[target]!=data:
        target=target.with_name(target.name+'.source-'+sha(source)[:16]+'.txt')
        assert not target.exists(),target
    if target in archiveBytes:assert archiveBytes[target]==data,target
    else:
        archiveBytes[target]=data
        refresh_pending.append((target,data,'Tools'))
    archive.append(dict(source=str(source),path=target.relative_to(r).as_posix(),sha256=sha(source)))
archive_target=r/archive_rel/'archive-manifest.json'
assert not archive_target.exists()
refresh_pending.append((archive_target,(json.dumps(dict(files=archive),indent=2)+'\n').encode(),'Tools'))
supplemental_review_path=r/archive_rel/'exact-joint-character-promotion-route-2096.json'

audit = r / "Extension/Dubon2026/Audit.lean"
at = audit.read_text(encoding="utf-8")
for n in queries:
    assert not re.search(r"``" + re.escape(n) + r"(?=[,\s])", at)
tm, dm = "\n]\n\nprivate def publicConstructions", "\n]\n\nprivate def runAudit"
assert at.count(tm) == at.count(dm) == 1
at = at.replace(tm, "".join("\n  ,``" + n for n in theorems) + tm, 1)
at = at.replace(dm, "".join("\n  ," + chr(96)*2 + n for n in defs) + dm, 1)
research_path = r / "Tools/lean-reuse-audit-20261020.json"
reuse_path = r / "Tools/source-exact-joint-character.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt9559"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> automorphy -> original all-weight characteristic-zero association -> arithmetic realization of the exact joint geometric/boundary operator character.'
discharged = 'The literal H1/parabolic-H1 quotient and its original Hecke action are constructed using native parabolic stability. Both this boundary quotient and the actual Tate diamond quotient are finite by existing results. A word that kills both actual operator spaces has square zero on the coefficient-reduced original integral H1. At twice the source precision, native congruence integrality and integrality of powers construct the original character at every requested precision. Proved original geometry supplies the actual quotient operators. The resulting character has whole-word pullback equal to the original Fourier-field character, without a supplied parabolic lift, unit boundary separator, exceptional integer or discrete valuation hypothesis. The prime range remains p greater than three.'
boundary = 'Arithmetic Galois realization of this exact joint algebra, primes two and three, two-dimensional characteristic-zero realization, original all-weight association, remaining local/image/regularity inputs, automorphy and literal higher symmetric-power continuation remain required. This does not construct a character on the geometric factor alone. Acceptance stays 16/20; DUB-17--20 OPEN; every original source and verification criterion is unchanged.'
status = 'The nine-module scratch scope passes 18 public axiom queries, 84 exhaustive theorem checks, sixteen linters per module and one declaration-value audit with 27 required dependencies, with zero diagnostics. Production aggregate, focused audits and sequential foundation/paper verification of the 9,568-module scope are pending.'
route = 'The expanded pinned public-source review and a renewed native-code search precede this route. Existing full-H1 transfer and finiteness, parabolic stability, Tate diamond-quotient finiteness, original geometric operators, congruence integrality and Mathlib IsIntegral.of_pow are reused directly. Retaining the literal boundary quotient removes the need for a new cusp-function carrier and a simultaneous boundary annihilator with unit character value in this finite descent. The previously prepared 26-module boundary-character promotion is deferred and was never executed. Only the nine modules consumed by the exact joint character are promoted. A duplicate scratch Tate-finiteness proof is preserved but omitted in favor of the existing theorem. All failed variants and diagnostics remain available. The first full audit rejected the explicit ring-instance name under defsWithUnderscore; its name was corrected and all affected canonical compilations and audits were rerun without suppressing the linter or changing a mathematical statement or value. Promotion changes imports only; accepted mathematical statements and proof bodies stay frozen. Paper, root pins, proof limits and owner-only BAT are unchanged.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Original character on the exact finite joint operator image (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 9,559-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
corrections = []
count = sum(z['exhaustiveTheorems'] for z in certs)
assert count == 84

docpaths = list(dict.fromkeys(r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]))
for f in docpaths:
    assert "\n\n" in f.read_text(encoding="utf-8")
readmes = [(r.parent / "README.md", "Current Project 83 status ("), (repo / "README.md", "Project 83 has an ")]
for f, prefix in readmes:
    assert sum(line.startswith(prefix) for line in f.read_text(encoding="utf-8").splitlines()) == 1
arch = r / "Dubon Architecture.md"
edge = '  GENUS9559["Original Gamma1 genus preservation at every nonzero level and away residue prime proved; actual quotient Hecke operators and arithmetic descent have no geometric premises. Parabolic transfer, association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourceExactJointCharacterProductionAudit9568.lean',p/'source-exact-joint-character-9568-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production9568.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/original-genus-consumers-20261116-2037'
registered = {row['path'] for row in c['files']}
for priorFile in priorArchive.iterdir():
    rel = priorFile.relative_to(r).as_posix()
    if priorFile.is_file() and rel not in registered:
        c['files'].append({'path': rel, 'role': 'Tools'})

reportSource = p / 'Dubon Exact Joint Character Assessment 2026-11-16.md'
assert sha(reportSource) == '41A47551AFAB2424C46B08179A7F162ACE84509C0E64EF2446BAD629991967A3'
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
    "productionModules": 9568, "modules": newmods, "queries": queries,
    "theoremRegistrations": theorems, "constructionRegistrations": defs,
    "sourceHashes": {mapping[t.stem]: sha(t) for t, _ in pending}, "scratchCertificates": certs,
    "exactDependency": dependency, "assumptionsDischarged": discharged, "stillOpen": boundary,
    "status": status, "rootPinsChanged": False, "proofLimitsChanged": False,
    "promotionChanges": 'Only canonical and versioned scratch imports are qualified to their registered production modules. All audited statements, proof bodies and comments remain identical. Original function fields and actual modular forms are retained; no assumption or completion criterion is weakened.',
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
arch.write_text(arch.read_text(encoding='utf-8').replace(edge,'  GENUS9559["Original Gamma1 genus preservation and actual geometric quotient Hecke operators proved (DUB-17/18)"] --> JOINT9568\n  JOINT9568["Original finite character constructed on exact geometric/boundary operator image; lift and separator premises removed. Arithmetic realization, exceptional primes, association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'),encoding='utf-8')



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Original character on the exact finite joint operator image - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-exact-joint-character.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub('  logInfo m!".*"\n', '  logInfo m!"SOURCE EXACT JOINT CHARACTER AUDIT PASS: {count} theorems including private/generated declarations. Original finite character on exact joint geometric/boundary algebra proved. Arithmetic realization and source gates OPEN;16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourceExactJointCharacterProductionAudit9568.lean").write_text(out, encoding="utf-8")
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
    target = p / (source.stem + "Production9568.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
(p / "source-exact-joint-character-9568-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 9568, "increment": 9, "queries": 18,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
