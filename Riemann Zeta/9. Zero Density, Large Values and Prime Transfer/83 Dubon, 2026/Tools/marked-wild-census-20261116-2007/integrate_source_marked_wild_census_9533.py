from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 9509
assert d["appliedSourceMarkedResidueFibers"]["receipt9509"]["exit"] == 0
assert (p / "paper-verification-9509-console.exit").read_text().strip() == "0"
assert (r/'Tools/marked-residue-fibers-20261029-1983/canonical-evidence-9509.json').exists()
key = "appliedSourceMarkedWildCensus"
assert key not in d
digests = {'source-marked-wild-different-1-scratch-receipt.json': '580CD8148D8866D29C24D1EB0CF44F08CF2D88017F78F20A25E3BEB02A60EA91', 'source-marked-wild-contribution-1-scratch-receipt.json': '832499BDEF972C68C36A12BB067A01CDD829D29AD4D1CC8B723729E342728593'}

for name, digest in digests.items():
    assert sha(p / name) == digest
certs = [json.loads((p / name).read_text(encoding="utf-8")) for name in digests]
mods = [m for z in certs for m in z["modules"]]
queries = [q for z in certs for q in z["queries"]]
theorems = [q for z in certs for q in z["theoremRegistrations"]]
defs = [q for z in certs for q in z["constructionRegistrations"]]
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (24, 24, 33, 30, 3)
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
archive_rel='Tools/marked-wild-census-20261116-2007'
evidence=[p/n for n in ['Dubon Marked Wild Census Assessment 2026-11-16.md', 'SourceMarkedCharTwoSignAction-2002.exit', 'SourceMarkedCharTwoSignAction-2002.log', 'SourceMarkedCharTwoSignAction.lean', 'SourceMarkedCharTwoSignAction1991a.exit', 'SourceMarkedCharTwoSignAction1991a.lean.txt', 'SourceMarkedCharTwoSignAction1991a.log', 'SourceMarkedCharTwoSignAction1991b.exit', 'SourceMarkedCharTwoSignAction1991b.lean', 'SourceMarkedCharTwoSignAction1991b.log', 'SourceMarkedDihedralFiberBound-2002.exit', 'SourceMarkedDihedralFiberBound-2002.log', 'SourceMarkedDihedralFiberBound.lean', 'SourceMarkedDihedralFiberBound1985a.exit', 'SourceMarkedDihedralFiberBound1985a.lean', 'SourceMarkedDihedralFiberBound1985a.log', 'SourceMarkedEmbeddingSignKernel-1984.exit', 'SourceMarkedEmbeddingSignKernel-1984.log', 'SourceMarkedEmbeddingSignKernel.lean', 'SourceMarkedEmbeddingSignKernel1975a.exit', 'SourceMarkedEmbeddingSignKernel1975a.lean', 'SourceMarkedEmbeddingSignKernel1975a.log', 'SourceMarkedFiberOrderRigidity-2002.exit', 'SourceMarkedFiberOrderRigidity-2002.log', 'SourceMarkedFiberOrderRigidity.lean', 'SourceMarkedFiberOrderRigidity1997a.exit', 'SourceMarkedFiberOrderRigidity1997a.lean.txt', 'SourceMarkedFiberOrderRigidity1997a.log', 'SourceMarkedFiberOrderRigidity1997b.exit', 'SourceMarkedFiberOrderRigidity1997b.lean', 'SourceMarkedFiberOrderRigidity1997b.log', 'SourceMarkedNormalOrderDescent-2002.exit', 'SourceMarkedNormalOrderDescent-2002.log', 'SourceMarkedNormalOrderDescent.lean', 'SourceMarkedNormalOrderDescent1993a.exit', 'SourceMarkedNormalOrderDescent1993a.lean', 'SourceMarkedNormalOrderDescent1993a.log', 'SourceMarkedOrderTwelveFiberBound-2002.exit', 'SourceMarkedOrderTwelveFiberBound-2002.log', 'SourceMarkedOrderTwelveFiberBound.lean', 'SourceMarkedOrderTwelveFiberBound1989a.exit', 'SourceMarkedOrderTwelveFiberBound1989a.lean.txt', 'SourceMarkedOrderTwelveFiberBound1989a.log', 'SourceMarkedOrderTwelveFiberBound1989b.exit', 'SourceMarkedOrderTwelveFiberBound1989b.lean.txt', 'SourceMarkedOrderTwelveFiberBound1989b.log', 'SourceMarkedOrderTwelveFiberBound1989c.exit', 'SourceMarkedOrderTwelveFiberBound1989c.lean', 'SourceMarkedOrderTwelveFiberBound1989c.log', 'SourceMarkedOriginalExactOrderThree-2002.exit', 'SourceMarkedOriginalExactOrderThree-2002.log', 'SourceMarkedOriginalExactOrderThree.lean', 'SourceMarkedOriginalExactOrderThree1999a.exit', 'SourceMarkedOriginalExactOrderThree1999a.lean', 'SourceMarkedOriginalExactOrderThree1999a.log', 'SourceMarkedOriginalExactOrderTwo-2002.exit', 'SourceMarkedOriginalExactOrderTwo-2002.log', 'SourceMarkedOriginalExactOrderTwo.lean', 'SourceMarkedOriginalExactOrderTwo1998a.exit', 'SourceMarkedOriginalExactOrderTwo1998a.lean', 'SourceMarkedOriginalExactOrderTwo1998a.log', 'SourceMarkedOriginalLocalDifferentials-1984.exit', 'SourceMarkedOriginalLocalDifferentials-1984.log', 'SourceMarkedOriginalLocalDifferentials.lean', 'SourceMarkedOriginalLocalDifferentials1979a.exit', 'SourceMarkedOriginalLocalDifferentials1979a.lean.txt', 'SourceMarkedOriginalLocalDifferentials1979a.log', 'SourceMarkedOriginalLocalDifferentials1979b.exit', 'SourceMarkedOriginalLocalDifferentials1979b.lean.txt', 'SourceMarkedOriginalLocalDifferentials1979b.log', 'SourceMarkedOriginalLocalDifferentials1979c.exit', 'SourceMarkedOriginalLocalDifferentials1979c.lean.txt', 'SourceMarkedOriginalLocalDifferentials1979c.log', 'SourceMarkedOriginalLocalDifferentials1979d.exit', 'SourceMarkedOriginalLocalDifferentials1979d.lean.txt', 'SourceMarkedOriginalLocalDifferentials1979d.log', 'SourceMarkedOriginalLocalDifferentials1979e.exit', 'SourceMarkedOriginalLocalDifferentials1979e.lean.txt', 'SourceMarkedOriginalLocalDifferentials1979e.log', 'SourceMarkedOriginalLocalDifferentials1979f.exit', 'SourceMarkedOriginalLocalDifferentials1979f.lean', 'SourceMarkedOriginalLocalDifferentials1979f.log', 'SourceMarkedOriginalNormalField-1984.exit', 'SourceMarkedOriginalNormalField-1984.log', 'SourceMarkedOriginalNormalField.lean', 'SourceMarkedOriginalNormalField1976a.exit', 'SourceMarkedOriginalNormalField1976a.lean.txt', 'SourceMarkedOriginalNormalField1976a.log', 'SourceMarkedOriginalNormalField1976b.exit', 'SourceMarkedOriginalNormalField1976b.lean', 'SourceMarkedOriginalNormalField1976b.log', 'SourceMarkedOriginalNormalFieldThree-1984.exit', 'SourceMarkedOriginalNormalFieldThree-1984.log', 'SourceMarkedOriginalNormalFieldThree.lean', 'SourceMarkedOriginalNormalFieldThree1978a.exit', 'SourceMarkedOriginalNormalFieldThree1978a.lean', 'SourceMarkedOriginalNormalFieldThree1978a.log', 'SourceMarkedOriginalNormalFieldTwo-1984.exit', 'SourceMarkedOriginalNormalFieldTwo-1984.log', 'SourceMarkedOriginalNormalFieldTwo.lean', 'SourceMarkedOriginalNormalFieldTwo1977a.exit', 'SourceMarkedOriginalNormalFieldTwo1977a.lean', 'SourceMarkedOriginalNormalFieldTwo1977a.log', 'SourceMarkedOriginalOrderBoundThree-2002.exit', 'SourceMarkedOriginalOrderBoundThree-2002.log', 'SourceMarkedOriginalOrderBoundThree.lean', 'SourceMarkedOriginalOrderBoundThree1995a.exit', 'SourceMarkedOriginalOrderBoundThree1995a.lean', 'SourceMarkedOriginalOrderBoundThree1995a.log', 'SourceMarkedOriginalOrderBoundTwo-2002.exit', 'SourceMarkedOriginalOrderBoundTwo-2002.log', 'SourceMarkedOriginalOrderBoundTwo.lean', 'SourceMarkedOriginalOrderBoundTwo1994a.exit', 'SourceMarkedOriginalOrderBoundTwo1994a.lean', 'SourceMarkedOriginalOrderBoundTwo1994a.log', 'SourceMarkedOriginalPositiveDegree-2002.exit', 'SourceMarkedOriginalPositiveDegree-2002.log', 'SourceMarkedOriginalPositiveDegree.lean', 'SourceMarkedOriginalPositiveDegree1996a.exit', 'SourceMarkedOriginalPositiveDegree1996a.lean.txt', 'SourceMarkedOriginalPositiveDegree1996a.log', 'SourceMarkedOriginalPositiveDegree1996b.exit', 'SourceMarkedOriginalPositiveDegree1996b.lean', 'SourceMarkedOriginalPositiveDegree1996b.log', 'SourceMarkedOriginalWildContributionThree-2002.exit', 'SourceMarkedOriginalWildContributionThree-2002.log', 'SourceMarkedOriginalWildContributionThree.lean', 'SourceMarkedOriginalWildContributionThree2001a.exit', 'SourceMarkedOriginalWildContributionThree2001a.lean', 'SourceMarkedOriginalWildContributionThree2001a.log', 'SourceMarkedOriginalWildContributionTwo-2002.exit', 'SourceMarkedOriginalWildContributionTwo-2002.log', 'SourceMarkedOriginalWildContributionTwo.lean', 'SourceMarkedOriginalWildContributionTwo2000a.exit', 'SourceMarkedOriginalWildContributionTwo2000a.lean', 'SourceMarkedOriginalWildContributionTwo2000a.log', 'SourceMarkedOriginalWildDifferent-1984.exit', 'SourceMarkedOriginalWildDifferent-1984.log', 'SourceMarkedOriginalWildDifferent.lean', 'SourceMarkedOriginalWildDifferent1980a.exit', 'SourceMarkedOriginalWildDifferent1980a.lean.txt', 'SourceMarkedOriginalWildDifferent1980a.log', 'SourceMarkedOriginalWildDifferent1980b.exit', 'SourceMarkedOriginalWildDifferent1980b.lean', 'SourceMarkedOriginalWildDifferent1980b.log', 'SourceMarkedOriginalWildDifferentThree-1984.exit', 'SourceMarkedOriginalWildDifferentThree-1984.log', 'SourceMarkedOriginalWildDifferentThree.lean', 'SourceMarkedOriginalWildDifferentThree1982a.exit', 'SourceMarkedOriginalWildDifferentThree1982a.lean', 'SourceMarkedOriginalWildDifferentThree1982a.log', 'SourceMarkedOriginalWildDifferentTwo-1984.exit', 'SourceMarkedOriginalWildDifferentTwo-1984.log', 'SourceMarkedOriginalWildDifferentTwo.lean', 'SourceMarkedOriginalWildDifferentTwo1981a.exit', 'SourceMarkedOriginalWildDifferentTwo1981a.lean', 'SourceMarkedOriginalWildDifferentTwo1981a.log', 'SourceMarkedOriginalWildFiberThree-2002.exit', 'SourceMarkedOriginalWildFiberThree-2002.log', 'SourceMarkedOriginalWildFiberThree.lean', 'SourceMarkedOriginalWildFiberThree1987a.exit', 'SourceMarkedOriginalWildFiberThree1987a.lean', 'SourceMarkedOriginalWildFiberThree1987a.log', 'SourceMarkedOriginalWildFiberTwo-2002.exit', 'SourceMarkedOriginalWildFiberTwo-2002.log', 'SourceMarkedOriginalWildFiberTwo.lean', 'SourceMarkedOriginalWildFiberTwo1992a.exit', 'SourceMarkedOriginalWildFiberTwo1992a.lean.txt', 'SourceMarkedOriginalWildFiberTwo1992a.log', 'SourceMarkedOriginalWildFiberTwo1992b.exit', 'SourceMarkedOriginalWildFiberTwo1992b.lean', 'SourceMarkedOriginalWildFiberTwo1992b.log', 'SourceMarkedSignActionHom-2002.exit', 'SourceMarkedSignActionHom-2002.log', 'SourceMarkedSignActionHom.lean', 'SourceMarkedSignActionHom1990a.exit', 'SourceMarkedSignActionHom1990a.lean', 'SourceMarkedSignActionHom1990a.log', 'SourceMarkedSignFiberSymmetries-2002.exit', 'SourceMarkedSignFiberSymmetries-2002.log', 'SourceMarkedSignFiberSymmetries.lean', 'SourceMarkedSignFiberSymmetries1986a.exit', 'SourceMarkedSignFiberSymmetries1986a.lean', 'SourceMarkedSignFiberSymmetries1986a.log', 'SourceMarkedWildContributionAudit1.exit', 'SourceMarkedWildContributionAudit1.lean', 'SourceMarkedWildContributionAudit1.log', 'SourceMarkedWildContributionDependencyAudit1.exit', 'SourceMarkedWildContributionDependencyAudit1.lean', 'SourceMarkedWildContributionDependencyAudit1.log', 'SourceMarkedWildContributionScratchOwnership2002.exit', 'SourceMarkedWildContributionScratchOwnership2002.lean', 'SourceMarkedWildContributionScratchOwnership2002.log', 'SourceMarkedWildDifferentAudit1.exit', 'SourceMarkedWildDifferentAudit1.lean', 'SourceMarkedWildDifferentAudit1.log', 'SourceMarkedWildDifferentDependencyAudit1.exit', 'SourceMarkedWildDifferentDependencyAudit1.lean', 'SourceMarkedWildDifferentDependencyAudit1.log', 'SourceMarkedWildDifferentScratchOwnership1984.exit', 'SourceMarkedWildDifferentScratchOwnership1984.lean', 'SourceMarkedWildDifferentScratchOwnership1984.log', 'audit_marked_wild_contribution_2002.ps1', 'audit_marked_wild_different_1984.ps1', 'build_marked_wild_contribution_canonical_2002.ps1', 'build_marked_wild_different_canonical_1984.ps1', 'marked-wild-census-promotion-route-2007.json', 'marked-wild-contribution-versions-2002.json', 'marked-wild-different-versions-1984.json', 'prepare_marked_wild_contribution_audit_2002.py', 'prepare_marked_wild_different_audit_1984.py', 'record_marked_wild_contribution_2002.py', 'record_marked_wild_different_1984.py', 'source-marked-wild-contribution-1-audit-config.json', 'source-marked-wild-contribution-1-reuse-review-20261116.json', 'source-marked-wild-contribution-1-scratch-receipt.json', 'source-marked-wild-contribution-audit-route-2002.json', 'source-marked-wild-different-1-audit-config.json', 'source-marked-wild-different-1-reuse-review-20261029.json', 'source-marked-wild-different-1-scratch-receipt.json', 'source-marked-wild-different-audit-route-1984.json']]
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
supplemental_review_path=r/archive_rel/'marked-wild-census-promotion-route-2007.json'

audit = r / "Extension/Dubon2026/Audit.lean"
at = audit.read_text(encoding="utf-8")
for n in queries:
    assert not re.search(r"``" + re.escape(n) + r"(?=[,\s])", at)
tm, dm = "\n]\n\nprivate def publicConstructions", "\n]\n\nprivate def runAudit"
assert at.count(tm) == at.count(dm) == 1
at = at.replace(tm, "".join("\n  ,``" + n for n in theorems) + tm, 1)
at = at.replace(dm, "".join("\n  ," + chr(96)*2 + n for n in defs) + dm, 1)
research_path = r / "Tools/lean-reuse-audit-20261020.json"
reuse_path = r / "Tools/source-marked-wild-census.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt9509"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> automorphy -> original all-weight characteristic-zero association -> homogeneous Gamma1 Hecke-character realization -> original genus preservation -> reverse genus -> original wild fiber orders and different contributions.'
discharged = 'For every original Gamma1 residue field in characteristic two or three away from N, with N greater than three, every positive j place has exact j order twelve or six respectively. Its different order is at least fourteen or seven respectively. Consequently six times the sum of differential orders over the actual original j=0 fiber is at least seven times the signed Gamma1 index in each wild characteristic. The normal fields, finite fiber charts, torsion actions, local differential generation and order divisibility are proved; none is retained as a premise in these endpoints.'
boundary = 'The original residue canonical-degree and Hurwitz comparison, the remaining small levels and reverse genus remain open in production. Original genus preservation, parabolic transfer, exceptional-prime removal, two-dimensional characteristic-zero realization, original all-weight association, remaining local/image/regularity inputs, automorphy and literal higher continuation remain required. Acceptance stays 16/20; DUB-17--20 OPEN; every original source and verification criterion is unchanged.'
status = 'The 24-module scratch scope passes 33 public axiom queries, 84 exhaustive theorem checks, sixteen linters per module and two declaration-value audits with 64 required dependencies, with zero diagnostics. Production aggregate, focused audits and sequential foundation/paper verification of the 9,533-module scope are pending.'
route = 'The November 16 public-source refresh found no directly reusable complete missing Dubon endpoint within its inspected scope. Native dihedral and order-twelve marks act freely on original exact-order point sign classes for N greater than three, avoiding a new finite-group classification or adapted torsion basis. Native finite normal-field descent, wild different bounds and exact separating-coordinate degree sums force the original local orders and summed contributions. Two independent scratch scopes pass 64 proof-VALUE dependencies, exhaustive public/private/generated axiom checks and sixteen linters per module. Failed versions and diagnostics are retained. Promotion changes imports only; statements, proof bodies and comments stay frozen. Exact ownership reconciliation and sequential foundation/paper verification remain mandatory. Paper, root pins, proof limits and owner-only BAT are unchanged.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Actual original Gamma1 wild orders and different contributions (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 9,509-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
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
edge = '  RESIDUEFIBERS9509["Actual original Gamma1 residue charts in all characteristics away from the level; tame elliptic fiber bounds for N greater than three proved. Wild census, small levels, reverse genus and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourceMarkedWildCensusProductionAudit9533.lean',p/'source-marked-wild-census-9533-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production9533.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/marked-residue-fibers-20261029-1983'
registered = {row['path'] for row in c['files']}
for priorFile in priorArchive.iterdir():
    rel = priorFile.relative_to(r).as_posix()
    if priorFile.is_file() and rel not in registered:
        c['files'].append({'path': rel, 'role': 'Tools'})

reportSource = p / 'Dubon Marked Wild Census Assessment 2026-11-16.md'
assert sha(reportSource) == 'AB8253EAA82E9ACDF7E01A69B1DAADE52F84C7D496A4001A9A7F0735E0D2B958'
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
    "productionModules": 9533, "modules": newmods, "queries": queries,
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
arch.write_text(arch.read_text(encoding='utf-8').replace(edge,'  RESIDUEFIBERS9509["Actual original residue charts and tame elliptic fiber bounds proved (DUB-17/18)"] --> WILDCENSUS9533\n  WILDCENSUS9533["Actual original wild orders twelve/six and different contributions fourteen/seven proved for N greater than three. Canonical degree, Hurwitz, small levels, reverse genus and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'),encoding='utf-8')



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Actual original Gamma1 wild orders and different contributions - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-marked-wild-census.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub('  logInfo m!".*"\n', '  logInfo m!"SOURCE MARKED WILD CENSUS AUDIT PASS: {count} theorems including private/generated declarations. Actual original wild orders and summed different contributions proved. Hurwitz, small levels, reverse genus and source gates OPEN;16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourceMarkedWildCensusProductionAudit9533.lean").write_text(out, encoding="utf-8")
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
    target = p / (source.stem + "Production9533.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
(p / "source-marked-wild-census-9533-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 9533, "increment": 24, "queries": 33,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
