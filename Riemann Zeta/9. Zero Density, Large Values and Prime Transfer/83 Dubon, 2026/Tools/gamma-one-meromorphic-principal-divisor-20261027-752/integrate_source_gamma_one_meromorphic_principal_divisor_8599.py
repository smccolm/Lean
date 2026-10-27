from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 8586
assert d["appliedSourceGammaOneFiniteChartsDivisors"]["receipt8586"]["exit"] == 0
assert (p / "paper-verification-8586b-console.exit").read_text().strip() == "0"
assert (r/'Tools/gamma-one-finite-charts-divisors-20261027-740/canonical-evidence-8586.json').exists()
key = "appliedSourceGammaOneMeromorphicPrincipalDivisor"
assert key not in d
digests = {'source-gamma-one-cusp-residues-1-scratch-receipt.json': '2F1EACCE6E23FDFFE316865260110175EA89ABA52C305803C7EB157D0D43B12F', 'source-gamma-one-cusp-exhaustion-1-scratch-receipt.json': '028C916EE20AD07A96B06F1AEB6F83C494D1A94FFC3B379066512A64801AA883', 'source-gamma-one-holomorphic-field-1-scratch-receipt.json': '32E41826F238016A886D15A69C61C38ECF954A56CB6EA71D9A4ABCF708D83AA8', 'source-gamma-one-pole-clearing-normalization-1-scratch-receipt.json': '7C5F0099EB393DC9052EE6BE5EDAEBB0D6B0F895155217BC73DD061D378B4F7A', 'source-gamma-one-meromorphic-field-1-scratch-receipt.json': 'FADC57811E5FCDBAEFC7F70DB4081EAE46685E6E3DCC1524A07A56A799AF6BF7', 'source-gamma-one-meromorphic-principal-divisor-1-scratch-receipt.json': 'CBFF760F67E11EA122C34E4604CCBEE59C9C032DBB22480205A75545D052B15C'}

for name, digest in digests.items():
    assert sha(p / name) == digest
certs = [json.loads((p / name).read_text(encoding="utf-8")) for name in digests]
mods = [m for z in certs for m in z["modules"]]
queries = [q for z in certs for q in z["queries"]]
theorems = [q for z in certs for q in z["theoremRegistrations"]]
defs = [q for z in certs for q in z["constructionRegistrations"]]
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (13, 13, 31, 31, 0)
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
archive_rel='Tools/gamma-one-meromorphic-principal-divisor-20261027-752'
evidence=[p/'gamma-one-meromorphic-principal-divisor-promotion-route-752.json']
evidence += [p/n for n in ['SourceGammaOneCuspBoundedRealization.exit', 'SourceGammaOneCuspBoundedRealization.lean', 'SourceGammaOneCuspBoundedRealization.log', 'SourceGammaOneCuspExhaustionAudit1.exit', 'SourceGammaOneCuspExhaustionAudit1.lean', 'SourceGammaOneCuspExhaustionAudit1.log', 'SourceGammaOneCuspExhaustionDependencyAudit1.exit', 'SourceGammaOneCuspExhaustionDependencyAudit1.lean', 'SourceGammaOneCuspExhaustionDependencyAudit1.log', 'SourceGammaOneCuspExhaustionScratchOwnership743.exit', 'SourceGammaOneCuspExhaustionScratchOwnership743.lean', 'SourceGammaOneCuspExhaustionScratchOwnership743.log', 'SourceGammaOneCuspPlaceExhaustion.exit', 'SourceGammaOneCuspPlaceExhaustion.lean', 'SourceGammaOneCuspPlaceExhaustion.log', 'SourceGammaOneCuspResidues.exit', 'SourceGammaOneCuspResidues.lean', 'SourceGammaOneCuspResidues.log', 'SourceGammaOneCuspResiduesAudit1.exit', 'SourceGammaOneCuspResiduesAudit1.lean', 'SourceGammaOneCuspResiduesAudit1.log', 'SourceGammaOneCuspResiduesDependencyAudit1.exit', 'SourceGammaOneCuspResiduesDependencyAudit1.lean', 'SourceGammaOneCuspResiduesDependencyAudit1.log', 'SourceGammaOneCuspResiduesScratchOwnership742.exit', 'SourceGammaOneCuspResiduesScratchOwnership742.lean', 'SourceGammaOneCuspResiduesScratchOwnership742.log', 'SourceGammaOneHolomorphicFieldAudit1.exit', 'SourceGammaOneHolomorphicFieldAudit1.lean', 'SourceGammaOneHolomorphicFieldAudit1.log', 'SourceGammaOneHolomorphicFieldDependencyAudit1.exit', 'SourceGammaOneHolomorphicFieldDependencyAudit1.lean', 'SourceGammaOneHolomorphicFieldDependencyAudit1.log', 'SourceGammaOneHolomorphicFieldRealization.exit', 'SourceGammaOneHolomorphicFieldRealization.lean', 'SourceGammaOneHolomorphicFieldRealization.log', 'SourceGammaOneHolomorphicFieldScratchOwnership744.exit', 'SourceGammaOneHolomorphicFieldScratchOwnership744.lean', 'SourceGammaOneHolomorphicFieldScratchOwnership744.log', 'SourceGammaOneHolomorphicModularQuotient.exit', 'SourceGammaOneHolomorphicModularQuotient.lean', 'SourceGammaOneHolomorphicModularQuotient.log', 'SourceGammaOneMeromorphicCuspLimits.exit', 'SourceGammaOneMeromorphicCuspLimits.lean', 'SourceGammaOneMeromorphicCuspLimits.log', 'SourceGammaOneMeromorphicFieldAudit1.exit', 'SourceGammaOneMeromorphicFieldAudit1.lean', 'SourceGammaOneMeromorphicFieldAudit1.log', 'SourceGammaOneMeromorphicFieldDependencyAudit1.exit', 'SourceGammaOneMeromorphicFieldDependencyAudit1.lean', 'SourceGammaOneMeromorphicFieldDependencyAudit1.log', 'SourceGammaOneMeromorphicFieldRealization.exit', 'SourceGammaOneMeromorphicFieldRealization.lean', 'SourceGammaOneMeromorphicFieldRealization.log', 'SourceGammaOneMeromorphicFieldScratchOwnership749.exit', 'SourceGammaOneMeromorphicFieldScratchOwnership749.lean', 'SourceGammaOneMeromorphicFieldScratchOwnership749.log', 'SourceGammaOneMeromorphicPrincipalDivisor.exit', 'SourceGammaOneMeromorphicPrincipalDivisor.lean', 'SourceGammaOneMeromorphicPrincipalDivisor.log', 'SourceGammaOneMeromorphicPrincipalDivisorAudit1.exit', 'SourceGammaOneMeromorphicPrincipalDivisorAudit1.lean', 'SourceGammaOneMeromorphicPrincipalDivisorAudit1.log', 'SourceGammaOneMeromorphicPrincipalDivisorDependencyAudit1.exit', 'SourceGammaOneMeromorphicPrincipalDivisorDependencyAudit1.lean', 'SourceGammaOneMeromorphicPrincipalDivisorDependencyAudit1.log', 'SourceGammaOneMeromorphicPrincipalDivisorScratchOwnership751.exit', 'SourceGammaOneMeromorphicPrincipalDivisorScratchOwnership751.lean', 'SourceGammaOneMeromorphicPrincipalDivisorScratchOwnership751.log', 'SourceGammaOneOriginalPoleMultiplier.exit', 'SourceGammaOneOriginalPoleMultiplier.lean', 'SourceGammaOneOriginalPoleMultiplier.log', 'SourceGammaOnePoleClearedCuspBounds.exit', 'SourceGammaOnePoleClearedCuspBounds.lean', 'SourceGammaOnePoleClearedCuspBounds.log', 'SourceGammaOnePoleClearedNormalization.exit', 'SourceGammaOnePoleClearedNormalization.lean', 'SourceGammaOnePoleClearedNormalization.log', 'SourceGammaOnePoleClearedProduct.exit', 'SourceGammaOnePoleClearedProduct.lean', 'SourceGammaOnePoleClearedProduct.log', 'SourceGammaOnePoleClearingNormalizationAudit1.exit', 'SourceGammaOnePoleClearingNormalizationAudit1.lean', 'SourceGammaOnePoleClearingNormalizationAudit1.log', 'SourceGammaOnePoleClearingNormalizationDependencyAudit1.exit', 'SourceGammaOnePoleClearingNormalizationDependencyAudit1.lean', 'SourceGammaOnePoleClearingNormalizationDependencyAudit1.log', 'SourceGammaOnePoleClearingNormalizationScratchOwnership746.exit', 'SourceGammaOnePoleClearingNormalizationScratchOwnership746.lean', 'SourceGammaOnePoleClearingNormalizationScratchOwnership746.log', 'SourceGammaOneUniformCuspPole.exit', 'SourceGammaOneUniformCuspPole.lean', 'SourceGammaOneUniformCuspPole.log', 'download_gamma_one_period_core_753.py', 'download_gamma_one_period_core_754.py', 'download_gamma_one_period_core_755.py', 'download_gamma_one_period_core_755b.py', 'gamma-one-cusp-exhaustion-audit-route-743.json', 'gamma-one-cusp-exhaustion-route-743.json', 'gamma-one-cusp-residues-audit-route-742.json', 'gamma-one-cusp-residues-route-742.json', 'gamma-one-holomorphic-field-audit-route-744.json', 'gamma-one-meromorphic-cusp-limits-route-750.json', 'gamma-one-meromorphic-field-assembly-route-749.json', 'gamma-one-meromorphic-field-audit-route-749.json', 'gamma-one-meromorphic-field-route-744.json', 'gamma-one-meromorphic-principal-divisor-audit-route-751.json', 'gamma-one-meromorphic-principal-divisor-route-751.json', 'gamma-one-original-pole-multiplier-route-745.json', 'gamma-one-pole-cleared-cusp-route-748.json', 'gamma-one-pole-cleared-normalization-route-746.json', 'gamma-one-pole-cleared-product-route-747.json', 'gamma-one-pole-clearing-normalization-audit-route-746.json', 'prepare_gamma_one_cusp_exhaustion_audit_743.py', 'prepare_gamma_one_cusp_residues_audit_742.py', 'prepare_gamma_one_holomorphic_field_audit_744.py', 'prepare_gamma_one_meromorphic_field_audit_749.py', 'prepare_gamma_one_meromorphic_principal_divisor_audit_751.py', 'prepare_gamma_one_pole_clearing_normalization_audit_746.py', 'record_gamma_one_cusp_exhaustion_743.py', 'record_gamma_one_cusp_residues_742.py', 'record_gamma_one_holomorphic_field_744.py', 'record_gamma_one_meromorphic_field_749.py', 'record_gamma_one_meromorphic_principal_divisor_751.py', 'record_gamma_one_pole_clearing_normalization_746.py', 'source-gamma-one-cusp-exhaustion-1-audit-config.json', 'source-gamma-one-cusp-exhaustion-1-reuse-review-20261027.json', 'source-gamma-one-cusp-exhaustion-1-scratch-receipt.json', 'source-gamma-one-cusp-residues-1-audit-config.json', 'source-gamma-one-cusp-residues-1-reuse-review-20261027.json', 'source-gamma-one-cusp-residues-1-scratch-receipt.json', 'source-gamma-one-holomorphic-field-1-audit-config.json', 'source-gamma-one-holomorphic-field-1-reuse-review-20261027.json', 'source-gamma-one-holomorphic-field-1-scratch-receipt.json', 'source-gamma-one-meromorphic-field-1-audit-config.json', 'source-gamma-one-meromorphic-field-1-reuse-review-20261027.json', 'source-gamma-one-meromorphic-field-1-scratch-receipt.json', 'source-gamma-one-meromorphic-principal-divisor-1-audit-config.json', 'source-gamma-one-meromorphic-principal-divisor-1-reuse-review-20261027.json', 'source-gamma-one-meromorphic-principal-divisor-1-scratch-receipt.json', 'source-gamma-one-pole-clearing-normalization-1-audit-config.json', 'source-gamma-one-pole-clearing-normalization-1-reuse-review-20261027.json', 'source-gamma-one-pole-clearing-normalization-1-scratch-receipt.json']]
for folder in ['gamma-one-cusp-exhaustion-failed-743a', 'gamma-one-cusp-exhaustion-failed-743b', 'gamma-one-cusp-residues-failed-742a', 'gamma-one-cusp-residues-failed-742b', 'gamma-one-meromorphic-cusp-limits-failed-750a', 'gamma-one-meromorphic-field-failed-744a', 'gamma-one-period-core-reuse-753', 'gamma-one-period-core-reuse-754', 'gamma-one-period-core-reuse-755', 'gamma-one-period-core-reuse-755b', 'gamma-one-pole-cleared-cusp-failed-748a', 'gamma-one-pole-cleared-normalization-failed-746a', 'gamma-one-pole-cleared-product-failed-747a', 'gamma-one-period-reuse-assessment-752']:
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
supplemental_review_path=r/archive_rel/'gamma-one-meromorphic-principal-divisor-promotion-route-752.json'

audit = r / "Extension/Dubon2026/Audit.lean"
at = audit.read_text(encoding="utf-8")
for n in queries:
    assert not re.search(r"``" + re.escape(n) + r"(?=[,\s])", at)
tm, dm = "\n]\n\nprivate def publicConstructions", "\n]\n\nprivate def runAudit"
assert at.count(tm) == at.count(dm) == 1
at = at.replace(tm, "".join("\n  ,``" + n for n in theorems) + tm, 1)
assert not defs  # This promotion adds only theorem registrations.
research_path = r / "Tools/lean-reuse-audit-20261020.json"
reuse_path = r / "Tools/source-gamma-one-meromorphic-principal-divisor.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt8586"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> arithmetic realization of original finite Gamma1 homogeneous-coefficient Hecke characters -> full/parabolic, transpose, diamond, Picard/H1 comparison -> actual differential and period geometry -> Abel-Jacobi principal-divisor converse.'
discharged = 'The exact invariant meromorphic-function contract gives a literal principal divisor in the original Gamma1 integral-ratio field. Actual cusp exhaustion follows from existing one-pole functions and weight-zero constancy. Finite-coordinate pole clearing and native meromorphic normalization construct a holomorphic product; discriminant powers control every translated cusp and actual modular-ratio membership returns the original field element. Exact analytic orders and every cusp order are derived. Nonzero translated limits force order zero at all j-pole places. No field-realization, cusp-exhaustion or cusp-order hypothesis is supplied to the final consumer.'
boundary = 'Constructing the meromorphic function from the Abel-Jacobi period condition still requires genuine real period surjectivity and reciprocity. Actual global periods and Hecke/diamond/Picard/H1, full/parabolic and transpose comparisons remain. Arithmetic realization of original finite homogeneous-coefficient Gamma1 characters, coefficient-field transport, Frobenius/inertia, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain. Complex semisimplicity, finite characters, Witt coefficients and universal deformation rings do not supply a characteristic-zero lift. 16/20; DUB-17--20 OPEN; all twenty gates unchanged.'
status = 'The thirteen-module original Gamma1 meromorphic principal-divisor conversion passes 31 public axiom queries, 40 exhaustive scratch theorem checks, sixteen linters per module and six declaration-value audits covering 79 required dependencies, with zero diagnostics. Production aggregate, focused audits and sequential foundation/paper verification of the 8,599-module scope are pending.'
route = 'The renewed search is recorded in Dubon Reuse Refresh 2026-10-27.md and Dubon Reuse Route Assessment 2026-10-27.md. Nine further pinned primary proof files were inspected. Existing local pole clearing, actual field membership and cusp functions give a shorter conversion than the candidate inverse-j/full-level-Galois cusp-order argument. The direct Gamma1 genus/Manin route and candidate principal-level period route are compared before expanding either. External import closures are not locally built. Only imports are qualified on promotion; audited statements and proof bodies remain identical. All failures and research snapshots are retained. Root pins, proof limits, source and full all-weight contract are unchanged.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Actual Gamma1 meromorphic principal-divisor conversion (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 8,586-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
corrections = []
count = sum(z['exhaustiveTheorems'] for z in certs)
assert count == 40

docpaths = list(dict.fromkeys(r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]))
for f in docpaths:
    assert "\n\n" in f.read_text(encoding="utf-8")
readmes = [(r.parent / "README.md", "Current Project 83 status ("), (repo / "README.md", "Project 83 has an ")]
for f, prefix in readmes:
    assert sum(line.startswith(prefix) for line in f.read_text(encoding="utf-8").splitlines()) == 1
arch = r / "Dubon Architecture.md"
edge = '  GAMMAONEFINITE8586["Exact elliptic ramification, normalized finite charts and analytic representatives of every divisor class proved. Global periods, Hecke/diamond/Picard/H1, all-weight arithmetic association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourceGammaOneMeromorphicPrincipalDivisorProductionAudit8599.lean',p/'source-gamma-one-meromorphic-principal-divisor-8599-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production8599.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/gamma-one-finite-charts-divisors-20261027-740'
registered = {row['path'] for row in c['files']}
for priorFile in priorArchive.iterdir():
    rel = priorFile.relative_to(r).as_posix()
    if priorFile.is_file() and rel not in registered:
        c['files'].append({'path': rel, 'role': 'Tools'})

reportSource = p / 'gamma-one-period-reuse-assessment-752/Dubon Reuse Route Assessment 2026-10-27.md'
assert sha(reportSource) == '5265FE0DF0B08207082C35A1B752D0568235A098823C87BFA9B0433230EB7D72'
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
    "productionModules": 8599, "modules": newmods, "queries": queries,
    "theoremRegistrations": theorems, "constructionRegistrations": defs,
    "sourceHashes": {mapping[t.stem]: sha(t) for t, _ in pending}, "scratchCertificates": certs,
    "exactDependency": dependency, "assumptionsDischarged": discharged, "stillOpen": boundary,
    "status": status, "rootPinsChanged": False, "proofLimitsChanged": False,
    "promotionChanges": 'Only scratch imports are qualified. All audited statements, proof bodies and comments remain identical. Exact actual field elements, normalized place orders, all nonzero Gamma1 levels and translated cusp limits are retained.',
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
arch.write_text(arch.read_text(encoding='utf-8').replace(edge,'  GAMMAONEFINITE8586["Exact elliptic ramification, normalized finite charts and analytic divisor representatives (DUB-17/18)"] --> GAMMAONEPRINCIPAL8599\n  GAMMAONEPRINCIPAL8599["Original-field meromorphic principal-divisor conversion and every cusp order proved. Function construction from periods, Hecke/diamond/Picard/H1, all-weight arithmetic association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'),encoding='utf-8')



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Actual Gamma1 meromorphic principal-divisor conversion - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-gamma-one-meromorphic-principal-divisor.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub('  logInfo m!".*"\n', '  logInfo m!"SOURCE GAMMA ONE MEROMORPHIC PRINCIPAL DIVISOR AUDIT PASS: {count} theorems including private/generated declarations. The exact meromorphic function gives a principal divisor in the original Gamma1 field with all cusp orders derived. Its construction from periods and original arithmetic comparison remain; 16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourceGammaOneMeromorphicPrincipalDivisorProductionAudit8599.lean").write_text(out, encoding="utf-8")
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
    target = p / (source.stem + "Production8599.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
(p / "source-gamma-one-meromorphic-principal-divisor-8599-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 8599, "increment": 13, "queries": 31,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
