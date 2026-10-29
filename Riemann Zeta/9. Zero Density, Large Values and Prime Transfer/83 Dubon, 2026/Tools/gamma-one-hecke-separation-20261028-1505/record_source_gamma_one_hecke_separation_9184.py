from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re, sys

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
c = json.loads((r / "Tools/scaffold.json").read_text(encoding="utf-8"))
assert len(c["productionModules"]) == 9184
dp = r / "Tools/lean-reuse-audit-20261015.json"
d = json.loads(dp.read_text(encoding="utf-8"))
k = d["appliedSourceGammaOneHeckeSeparation"]
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
bad = r"(^|\s)(warning:|error(?:\(|:)|PANIC\b)|Try this:|Found [1-9][0-9]* errors|fatal exception|sorryAx"
for module, digest in k["sourceHashes"].items():
    assert sha(r / "Extension" / (module.replace(".", "/") + ".lean")) == digest, module
old = k["status"]
ownershipComparison = json.loads((p / "source-gamma-one-hecke-separation-ownership-comparison-9184.json").read_text())
assert ownershipComparison['scratchSum'] == 270
assert ownershipComparison['productionNamesNotInScratch'] == ownershipComparison['unexplainedMissing'] == []
assert set(ownershipComparison['missingFromFocused']) == set(ownershipComparison['missingFromFocusedAlreadyInPrevious'])
assert ownershipComparison['productionFocused'] == ownershipComparison['scratchDistinct'] - len(ownershipComparison['missingFromFocused'])

for item in [x['log'] for x in ownershipComparison['scopes']] + [
        ownershipComparison['productionOwnership'], ownershipComparison['previousGlobal']]:
    f = Path(item['path'])
    assert sha(f) == item['sha256']
    if 'sourceSha256' in item:
        assert sha(f.with_suffix('.lean')) == item['sourceSha256']
if sys.argv[1] == "--focused":
    key = "productionFocusedReceipt9184"
    build = p / "source-gamma-one-hecke-separation-production-build-9184.log"
    assert build.with_suffix(".exit").read_text().strip() == "0"
    bt = build.read_text(encoding="utf-16")
    assert "Build completed successfully" in bt and not re.search(bad, bt)
    log = p / "SourceGammaOneHeckeSeparationProductionAudit9184.log"
    assert log.with_suffix(".exit").read_text().strip() == "0"
    t = log.read_text(encoding="utf-16")
    assert not re.search(bad, t)
    found = re.findall(r"^'(.+)' depends on axioms:\s*\[([^]]*)\]", t, re.M)
    free = re.findall(r"^'(.+)' does not depend on any axioms", t, re.M)
    assert {n for n, _ in found} | set(free) == set(k["queries"])
    for name, axioms in found:
        assert set(x.strip() for x in axioms.split(",") if x.strip()) <= {"propext", "Classical.choice", "Quot.sound"}, name
    assert t.count("All linting checks passed!") == 35
    count = int(re.search(r"SOURCE GAMMA ONE HECKE SEPARATION AUDIT PASS: (\d+) theorems", t)[1])
    assert sum(z["exhaustiveTheorems"] for z in k["scratchCertificates"]) == 270
    assert count == ownershipComparison['productionFocused']
    focused = log.with_suffix(".lean").read_text(encoding="utf-8")
    scopes = re.findall(r"^#lint in (\S+)", focused, re.M)
    audited = re.findall(r"`([\w.]+)", re.search(r"let modules : Array Name := #\[([^]]+)\]", focused)[1])
    assert set(scopes) == set(audited) == set(k["modules"]) and len(k["modules"]) == 35
    deps = []
    filenames = json.loads((p / "source-gamma-one-hecke-separation-9184-production-audits.json").read_text())
    assert len(filenames) == len(k["scratchCertificates"]) == len(ownershipComparison["scopes"]) == 5
    for filename, cert in zip(filenames, k["scratchCertificates"]):
        dep = p / (filename + ".log")
        assert dep.with_suffix(".exit").read_text().strip() == "0"
        dt = dep.read_text(encoding="utf-16")
        assert "DEPENDENCY AUDIT PASS:" in dt and not re.search(bad, dt)
        assert re.search(r"all " + str(cert["requiredProofValueEdges"]) + r" required (?:proof )?dependencies", dt)
        deps.append({"log": str(dep), "sha256": sha(dep),
            "requiredProofValueEdges": cert["requiredProofValueEdges"],
            "consumers": cert["consumers"], "sourceSha256": sha(dep.with_suffix(".lean"))})
    receipt = {"proofDependencyAudits": deps, "log": str(log), "sha256": sha(log),
        "aggregateLog": str(build), "aggregateSha256": sha(build), "productionModules": 9184,
        "incrementModules": 35, "axiomChecks": len(k["queries"]), "exhaustiveIncrementTheorems": count,
        "linterScopes": 35, "lintersPerScope": 16, "exit": 0, "diagnostics": 0,
        "scratchExhaustiveTheorems": 270,
        "productionReuse": k["promotionChanges"],
        "omittedScratchTheorems": k["omittedScratchTheorems"],
        "existingReuseTheorems": k["existingReuseTheorems"]}
    new = 'The 9,184-module production aggregate and focused original Gamma One Hecke characters and integral separation audit pass with zero diagnostics. Five declaration-value audits verify 145 required dependency checks. ' + k['stillOpen'] + ' Sequential foundation/paper verification of this scope is pending.'
    heading = 'Production original Gamma One Hecke characters and integral separation pending full run - ' + k['date']




else:
    assert sys.argv[1] == "--canonical" and k["productionFocusedReceipt9184"]["exit"] == 0
    key = "receipt9184"
    assert (p / "root-verification-9184-console.exit").read_text().strip() == "0"
    assert (p / "paper-verification-9184-console.exit").read_text().strip() == "0"
    pc = (p / "paper-verification-9184-console.log").read_text(encoding="utf-16")
    rc = (p / "root-verification-9184-console.log").read_text(encoding="utf-16")
    paper = Path(re.findall(r"^Log: (.+)$", pc, re.M)[-1].strip())
    assert paper.parent == r / "logs"
    root = repo / "logs" / re.findall(r"foundation_freeze_\d{8}_\d{6}\.log", rc)[-1]
    t, rt = paper.read_text(encoding="utf-8-sig"), root.read_text(encoding="utf-8-sig")
    assert "FINAL RESULT: PASS" in rt
    assert "DEVELOPMENT PASS - IMPLEMENTED SCOPE VERIFIED; 16/20 GATES COMPLETE; PAPER INCOMPLETE" in t
    assert len(re.findall(r"^PASS: sorry/admit/sorryAx$", rt, re.M)) == 1
    assert not re.search(bad, t)
    assert not re.search(bad, re.sub(r"^PASS: sorry/admit/sorryAx$", "", rt, flags=re.M))
    for module in c["verificationModules"]:
        assert f"PASS: {module}; exit 0; zero Lean diagnostics" in t, module
    a = re.search(r"AUDIT PASS: (\d+) project theorems.*?; (\d+) registered consumers", t)
    b = re.search(r"Found 0 errors in (\d+) declarations \(plus (\d+) automatically generated ones\).*?with (\d+) linters", t)
    constructions = re.search(r"; (\d+) registered constructions", t)
    assert constructions and int(constructions[1]) == (
        d["appliedSourceGammaOneGlobalGalois"]["receipt9149"]["registeredConstructions"]
        + len(k["constructionRegistrations"]))
    ownershipLog = p / "SourceGammaOneHeckeSeparationOwnership9184.log"
    assert ownershipLog.with_suffix(".exit").read_text().strip() == "0"
    ot = ownershipLog.read_text(encoding="utf-16")
    assert not re.search(bad, ot)
    focusedNames = set(re.findall(r"^OWNER \S+: (\S+)$", ot, re.M))
    assert len(focusedNames) == ownershipComparison['productionFocused']
    previous = r / d["appliedSourceGammaOneGlobalGalois"]["receipt9149"]["log"]
    previousText = previous.read_text(encoding="utf-8-sig")
    names = lambda text: set(re.findall(r"PASS ([^:\s]+): \[", text))
    oldNames, newNames = names(previousText), names(t)
    assert len(oldNames) == d['appliedSourceGammaOneGlobalGalois']['receipt9149']['projectTheorems']
    globalLog = p / 'SourceGammaOneHeckeSeparationGlobalOwnership9184.log'
    assert globalLog.with_suffix('.exit').read_text().strip() == '0'
    gt = globalLog.read_text(encoding='utf-16')
    assert not re.search(bad, gt)
    assert globalLog.stat().st_mtime >= globalLog.with_suffix('.lean').stat().st_mtime
    globalRows = {name: (owner, ty, val) for owner, name, ty, val in
        re.findall(r'^GLOBAL (\S+): (\S+) (\d+) (\d+)$', gt, re.M)}
    focusedRows = {name: (ty, val) for name, ty, val in
        re.findall(r'^FINGERPRINT (\S+): (\d+) (\d+)$', ot, re.M)}
    assert set(globalRows) == set(focusedRows) == focusedNames
    for name in focusedNames:
        assert globalRows[name][1:] == focusedRows[name], name
    upstreamGenerated = {name for name, (owner, _, _) in globalRows.items()
        if not owner.startswith('Dubon2026.')}
    assert not (oldNames & upstreamGenerated)
    assert newNames == (oldNames | focusedNames) - upstreamGenerated
    expected = len((oldNames | focusedNames) - upstreamGenerated)
    countReconciliation = dict(previousTheorems=len(oldNames), focusedTheorems=len(focusedNames),
        sharedGeneratedNames=sorted(oldNames & focusedNames), addedTheorems=len(focusedNames-oldNames-upstreamGenerated),
        removedTheorems=[], upstreamOwnedGeneratedNames=sorted(upstreamGenerated), globalOwnershipLog=str(globalLog), globalOwnershipSha256=sha(globalLog), globalOwnershipSourceSha256=sha(globalLog.with_suffix('.lean')), globalOwnershipReason='Every focused theorem is retained with the same type and value hashes and standard logical axioms in the exact full import environment. Generated names owned by upstream modules there are recorded separately from the project-owned exhaustive count.', ownershipLog=str(ownershipLog), ownershipSha256=sha(ownershipLog))
    assert a and int(a[1]) == expected and int(a[2]) == 26760 and b and int(b[3]) == 16 and len(c["verificationModules"]) == 14
    for name in k["constructionRegistrations"]:
        assert "PASS CONSTRUCTION " + name + ":" in t, name
    receipt = {"recordedUTC": datetime.now(timezone.utc).isoformat(), "log": paper.relative_to(r).as_posix(),
        "sha256": sha(paper), "bytes": paper.stat().st_size, "exit": 0, "diagnostics": 0,
        "productionModules": 9184, "projectTheorems": int(a[1]), "registeredConsumers": int(a[2]),
        "registeredConstructions": int(constructions[1]), "declarations": int(b[1]),
        "generated": int(b[2]), "linters": 16, "regressions": 13,
        "foundationLog": root.relative_to(repo).as_posix(), "foundationSha256": sha(root),
        "countReconciliation": countReconciliation}
    new = (f"Sequential foundation/paper verification passes with zero diagnostics for the 9,184-module scope: "
        f"all thirteen retained regressions, {int(a[1]):,} exhaustive theorem checks, "
        f"{int(a[2]):,} registered consumers and sixteen linters. "
        "The reproduction manifest records the receipt; acceptance remains 16/20 and DUB-17-20 remain open.")
    heading = "Verified original Gamma One Hecke characters and integral separation - " + k["date"]
assert key not in k
receipt['scratchToProductionOwnership'] = ownershipComparison
receipt['scratchToProductionCountReason'] = (
    f"All {ownershipComparison['scratchDistinct']} distinct names from "
    f"{ownershipComparison['scratchSum']} exhaustive scratch checks are retained: "
    f"{ownershipComparison['productionFocused']} in the production focused scope and "
    f"{len(ownershipComparison['missingFromFocused'])} previously audited generated names. "
    "Exact name-set comparison explains any ownership changes; no unaccounted theorem is missing.")

receipt["boundary"] = k["stillOpen"]
paths = {r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]}
paths |= {r.parent / "README.md", repo / "README.md", r / 'Dubon Original Gamma One Hecke and Separation Assessment 2026-10-28.md'}
for f in paths:
    assert old in f.read_text(encoding="utf-8"), str(f)
research_path = r / "Tools/lean-reuse-audit-20261020.json"
reuse_path = r / "Tools/source-gamma-one-hecke-separation.json"
research, reuse = (json.loads(f.read_text(encoding="utf-8")) for f in (research_path, reuse_path))
assert research["status"] == reuse["status"] == old
k[key], k["status"] = receipt, new
research[key], research["status"] = receipt, new
reuse[key], reuse["status"] = receipt, new
if sys.argv[1] == '--canonical' and 'postFocusedCommentRepair' in k:
    repair = k['postFocusedCommentRepair']
    repair['postRepairVerification'] = dict(foundationLog=receipt['foundationLog'],
        foundationSha256=receipt['foundationSha256'],paperLog=receipt['log'],
        paperSha256=receipt['sha256'],exit=0,diagnostics=0,
        reason='The sequential canonical run recompiles changed production comments and dependants, checks every production theorem and reruns all thirteen regressions. Proof bodies remain identical to the focused scope.')
    research['postFocusedCommentRepair'] = repair
    reuse['postFocusedCommentRepair'] = repair
dp.write_text(json.dumps(d, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
research_path.write_text(json.dumps(research, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
reuse_path.write_text(json.dumps(reuse, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
for f in paths:
    f.write_text(f.read_text(encoding="utf-8").replace(old, new), encoding="utf-8")
f = r / "Dubon Reproduction Manifest.md"
t = f.read_text(encoding="utf-8")
assert "## " + heading not in t
f.write_text(t + "\n## " + heading + "\n\n" + new + "\n\n" + k["stillOpen"] +
    "\n\n```json\n" + json.dumps(receipt, indent=2) + "\n```\n", encoding="utf-8")
print(json.dumps(receipt))
