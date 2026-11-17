from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

p = Path(__file__).parent
repo = Path(r"E:\Lean\Riemann Zeta")
r = repo / "9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026"
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
cp, dp = r / "Tools/scaffold.json", r / "Tools/lean-reuse-audit-20261015.json"
c, d = (json.loads(f.read_text(encoding="utf-8")) for f in (cp, dp))
assert len(c["productionModules"]) == 9533
assert d["appliedSourceMarkedWildCensus"]["receipt9533"]["exit"] == 0
assert (p / "paper-verification-9533-console.exit").read_text().strip() == "0"
assert (r/'Tools/marked-wild-census-20261116-2007/canonical-evidence-9533.json').exists()
key = "appliedSourceOriginalGenusConsumers"
assert key not in d
digests = {'source-gammaone-genus-comparison-1-scratch-receipt.json': 'F7B118B5905BD9106EAA6AB219E4D4637367164771F8BB5F582FDB4F66ED06F3', 'source-original-genus-preservation-1-scratch-receipt.json': '281E1B1B28C1E520B5C7BEC13D8495B4C1942066C83C9F7DEC30CAB625274D3E', 'source-gammaone-geometric-consumers-1-scratch-receipt.json': 'A1C5475B9543910A3A85FE55E4ACF8397F457469A82E6A7536A0C6D95D2AB1E5'}

for name, digest in digests.items():
    assert sha(p / name) == digest
certs = [json.loads((p / name).read_text(encoding="utf-8")) for name in digests]
mods = [m for z in certs for m in z["modules"]]
queries = [q for z in certs for q in z["queries"]]
theorems = [q for z in certs for q in z["theoremRegistrations"]]
defs = [q for z in certs for q in z["constructionRegistrations"]]
assert (len(mods), len(set(mods)), len(queries), len(theorems), len(defs)) == (26, 26, 46, 45, 1)
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
archive_rel='Tools/original-genus-consumers-20261116-2037'
evidence=[p/n for n in ['Dubon Original Genus and Consumers Assessment 2026-11-16.md', 'SourceCurveSeparatingCoordinateCanonical-2027.exit', 'SourceCurveSeparatingCoordinateCanonical-2027.log', 'SourceCurveSeparatingCoordinateCanonical.lean', 'SourceCurveSeparatingCoordinateCanonical2009a.exit', 'SourceCurveSeparatingCoordinateCanonical2009a.lean', 'SourceCurveSeparatingCoordinateCanonical2009a.log', 'SourceCurveSeparatingCoordinateCanonicalDegree-2027.exit', 'SourceCurveSeparatingCoordinateCanonicalDegree-2027.log', 'SourceCurveSeparatingCoordinateCanonicalDegree.lean', 'SourceCurveSeparatingCoordinateCanonicalDegree2012a.exit', 'SourceCurveSeparatingCoordinateCanonicalDegree2012a.lean', 'SourceCurveSeparatingCoordinateCanonicalDegree2012a.log', 'SourceCurveSeparatingCoordinateGeometry-2027.exit', 'SourceCurveSeparatingCoordinateGeometry-2027.log', 'SourceCurveSeparatingCoordinateGeometry.lean', 'SourceCurveSeparatingCoordinateGeometry2008a.exit', 'SourceCurveSeparatingCoordinateGeometry2008a.lean', 'SourceCurveSeparatingCoordinateGeometry2008a.log', 'SourceCurveSeparatingCoordinateGlobalResidues-2027.exit', 'SourceCurveSeparatingCoordinateGlobalResidues-2027.log', 'SourceCurveSeparatingCoordinateGlobalResidues.lean', 'SourceCurveSeparatingCoordinateGlobalResidues2010a.exit', 'SourceCurveSeparatingCoordinateGlobalResidues2010a.lean', 'SourceCurveSeparatingCoordinateGlobalResidues2010a.log', 'SourceCurveSeparatingCoordinateHurwitz-2027.exit', 'SourceCurveSeparatingCoordinateHurwitz-2027.log', 'SourceCurveSeparatingCoordinateHurwitz.lean', 'SourceCurveSeparatingCoordinateHurwitz2013a.exit', 'SourceCurveSeparatingCoordinateHurwitz2013a.lean.txt', 'SourceCurveSeparatingCoordinateHurwitz2013a.log', 'SourceCurveSeparatingCoordinateHurwitz2013b.exit', 'SourceCurveSeparatingCoordinateHurwitz2013b.lean.txt', 'SourceCurveSeparatingCoordinateHurwitz2013b.log', 'SourceCurveSeparatingCoordinateHurwitz2013c.exit', 'SourceCurveSeparatingCoordinateHurwitz2013c.lean', 'SourceCurveSeparatingCoordinateHurwitz2013c.log', 'SourceCurveSeparatingCoordinateResidueDuality-2027.exit', 'SourceCurveSeparatingCoordinateResidueDuality-2027.log', 'SourceCurveSeparatingCoordinateResidueDuality.lean', 'SourceCurveSeparatingCoordinateResidueDuality2011a.exit', 'SourceCurveSeparatingCoordinateResidueDuality2011a.lean.txt', 'SourceCurveSeparatingCoordinateResidueDuality2011a.log', 'SourceCurveSeparatingCoordinateResidueDuality2011b.exit', 'SourceCurveSeparatingCoordinateResidueDuality2011b.lean', 'SourceCurveSeparatingCoordinateResidueDuality2011b.log', 'SourceCurveSeparatingFiberSums-2027.exit', 'SourceCurveSeparatingFiberSums-2027.log', 'SourceCurveSeparatingFiberSums.lean', 'SourceCurveSeparatingFiberSums2020a.exit', 'SourceCurveSeparatingFiberSums2020a.lean.txt', 'SourceCurveSeparatingFiberSums2020a.log', 'SourceCurveSeparatingFiberSums2020b.exit', 'SourceCurveSeparatingFiberSums2020b.lean', 'SourceCurveSeparatingFiberSums2020b.log', 'SourceCurveSeparatingHurwitzBound-2027.exit', 'SourceCurveSeparatingHurwitzBound-2027.log', 'SourceCurveSeparatingHurwitzBound.lean', 'SourceCurveSeparatingHurwitzBound2015a.exit', 'SourceCurveSeparatingHurwitzBound2015a.lean', 'SourceCurveSeparatingHurwitzBound2015a.log', 'SourceCurveSeparatingHurwitzCuspBound-2027.exit', 'SourceCurveSeparatingHurwitzCuspBound-2027.log', 'SourceCurveSeparatingHurwitzCuspBound.lean', 'SourceCurveSeparatingHurwitzCuspBound2017a.exit', 'SourceCurveSeparatingHurwitzCuspBound2017a.lean.txt', 'SourceCurveSeparatingHurwitzCuspBound2017a.log', 'SourceCurveSeparatingHurwitzCuspBound2017b.exit', 'SourceCurveSeparatingHurwitzCuspBound2017b.lean', 'SourceCurveSeparatingHurwitzCuspBound2017b.log', 'SourceCurveSeparatingPoleSums-2027.exit', 'SourceCurveSeparatingPoleSums-2027.log', 'SourceCurveSeparatingPoleSums.lean', 'SourceCurveSeparatingPoleSums2016a.exit', 'SourceCurveSeparatingPoleSums2016a.lean.txt', 'SourceCurveSeparatingPoleSums2016a.log', 'SourceCurveSeparatingPoleSums2016b.exit', 'SourceCurveSeparatingPoleSums2016b.lean', 'SourceCurveSeparatingPoleSums2016b.log', 'SourceGammaOneArithmeticGenus-2014.exit', 'SourceGammaOneArithmeticGenus-2014.log', 'SourceGammaOneArithmeticGenus.lean', 'SourceGammaOneArithmeticGenus2005a.exit', 'SourceGammaOneArithmeticGenus2005a.lean', 'SourceGammaOneArithmeticGenus2005a.log', 'SourceGammaOneArithmeticGenusBound-2014.exit', 'SourceGammaOneArithmeticGenusBound-2014.log', 'SourceGammaOneArithmeticGenusBound.lean', 'SourceGammaOneArithmeticGenusBound2006a.exit', 'SourceGammaOneArithmeticGenusBound2006a.lean', 'SourceGammaOneArithmeticGenusBound2006a.log', 'SourceGammaOneConormDimension-2014.exit', 'SourceGammaOneConormDimension-2014.log', 'SourceGammaOneConormDimension.lean', 'SourceGammaOneConormDimension2004a.exit', 'SourceGammaOneConormDimension2004a.lean.txt', 'SourceGammaOneConormDimension2004a.log', 'SourceGammaOneConormDimension2004b.exit', 'SourceGammaOneConormDimension2004b.lean', 'SourceGammaOneConormDimension2004b.log', 'SourceGammaOneConormDivisorSpaces-2014.exit', 'SourceGammaOneConormDivisorSpaces-2014.log', 'SourceGammaOneConormDivisorSpaces.lean', 'SourceGammaOneConormDivisorSpaces2003a.exit', 'SourceGammaOneConormDivisorSpaces2003a.lean', 'SourceGammaOneConormDivisorSpaces2003a.log', 'SourceGammaOneGenusComparisonAudit1.exit', 'SourceGammaOneGenusComparisonAudit1.lean', 'SourceGammaOneGenusComparisonAudit1.log', 'SourceGammaOneGenusComparisonDependencyAudit1.exit', 'SourceGammaOneGenusComparisonDependencyAudit1.lean', 'SourceGammaOneGenusComparisonDependencyAudit1.log', 'SourceGammaOneGenusComparisonScratchOwnership2014.exit', 'SourceGammaOneGenusComparisonScratchOwnership2014.lean', 'SourceGammaOneGenusComparisonScratchOwnership2014.log', 'SourceGammaOneGeometricArithmeticDescent-2032.exit', 'SourceGammaOneGeometricArithmeticDescent-2032.log', 'SourceGammaOneGeometricArithmeticDescent.lean', 'SourceGammaOneGeometricArithmeticDescent2030a.exit', 'SourceGammaOneGeometricArithmeticDescent2030a.lean', 'SourceGammaOneGeometricArithmeticDescent2030a.log', 'SourceGammaOneGeometricCharacter-2032.exit', 'SourceGammaOneGeometricCharacter-2032.log', 'SourceGammaOneGeometricCharacter.lean', 'SourceGammaOneGeometricCharacter2031a.exit', 'SourceGammaOneGeometricCharacter2031a.lean', 'SourceGammaOneGeometricCharacter2031a.log', 'SourceGammaOneGeometricConsumersAudit1.exit', 'SourceGammaOneGeometricConsumersAudit1.lean', 'SourceGammaOneGeometricConsumersAudit1.log', 'SourceGammaOneGeometricConsumersDependencyAudit1.exit', 'SourceGammaOneGeometricConsumersDependencyAudit1.lean.txt', 'SourceGammaOneGeometricConsumersDependencyAudit1.log', 'SourceGammaOneGeometricConsumersDependencyAudit1b.exit', 'SourceGammaOneGeometricConsumersDependencyAudit1b.lean', 'SourceGammaOneGeometricConsumersDependencyAudit1b.log', 'SourceGammaOneGeometricConsumersScratchOwnership2032.exit', 'SourceGammaOneGeometricConsumersScratchOwnership2032.lean', 'SourceGammaOneGeometricConsumersScratchOwnership2032.log', 'SourceGammaOneGeometricHeckeFamily-2032.exit', 'SourceGammaOneGeometricHeckeFamily-2032.log', 'SourceGammaOneGeometricHeckeFamily.lean', 'SourceGammaOneGeometricHeckeFamily2029a.exit', 'SourceGammaOneGeometricHeckeFamily2029a.lean', 'SourceGammaOneGeometricHeckeFamily2029a.log', 'SourceGammaOneLocalGoodReduction-2032.exit', 'SourceGammaOneLocalGoodReduction-2032.log', 'SourceGammaOneLocalGoodReduction.lean', 'SourceGammaOneLocalGoodReduction2028a.exit', 'SourceGammaOneLocalGoodReduction2028a.lean.txt', 'SourceGammaOneLocalGoodReduction2028a.log', 'SourceGammaOneLocalGoodReduction2028b.exit', 'SourceGammaOneLocalGoodReduction2028b.lean', 'SourceGammaOneLocalGoodReduction2028b.log', 'SourceGammaOneSmallLevelGenus-2027.exit', 'SourceGammaOneSmallLevelGenus-2027.log', 'SourceGammaOneSmallLevelGenus.lean', 'SourceGammaOneSmallLevelGenus2025a.exit', 'SourceGammaOneSmallLevelGenus2025a.lean', 'SourceGammaOneSmallLevelGenus2025a.log', 'SourceGammaOneSmallLevelIndex-2027.exit', 'SourceGammaOneSmallLevelIndex-2027.log', 'SourceGammaOneSmallLevelIndex.lean', 'SourceGammaOneSmallLevelIndex2024a.exit', 'SourceGammaOneSmallLevelIndex2024a.lean.txt', 'SourceGammaOneSmallLevelIndex2024a.log', 'SourceGammaOneSmallLevelIndex2024b.exit', 'SourceGammaOneSmallLevelIndex2024b.lean', 'SourceGammaOneSmallLevelIndex2024b.log', 'SourceOriginalGammaOneGenusPreservation-2027.exit', 'SourceOriginalGammaOneGenusPreservation-2027.log', 'SourceOriginalGammaOneGenusPreservation.lean', 'SourceOriginalGammaOneGenusPreservation2026a.exit', 'SourceOriginalGammaOneGenusPreservation2026a.lean.txt', 'SourceOriginalGammaOneGenusPreservation2026a.log', 'SourceOriginalGammaOneGenusPreservation2026b.exit', 'SourceOriginalGammaOneGenusPreservation2026b.lean', 'SourceOriginalGammaOneGenusPreservation2026b.log', 'SourceOriginalGenusPreservationAudit1.exit', 'SourceOriginalGenusPreservationAudit1.lean', 'SourceOriginalGenusPreservationAudit1.log', 'SourceOriginalGenusPreservationDependencyAudit1.exit', 'SourceOriginalGenusPreservationDependencyAudit1.lean', 'SourceOriginalGenusPreservationDependencyAudit1.log', 'SourceOriginalGenusPreservationScratchOwnership2027.exit', 'SourceOriginalGenusPreservationScratchOwnership2027.lean', 'SourceOriginalGenusPreservationScratchOwnership2027.log', 'SourceOriginalLargeLevelGenusLower-2027.exit', 'SourceOriginalLargeLevelGenusLower-2027.log', 'SourceOriginalLargeLevelGenusLower.lean', 'SourceOriginalLargeLevelGenusLower2023a.exit', 'SourceOriginalLargeLevelGenusLower2023a.lean', 'SourceOriginalLargeLevelGenusLower2023a.log', 'SourceOriginalResidueHurwitz-2027.exit', 'SourceOriginalResidueHurwitz-2027.log', 'SourceOriginalResidueHurwitz.lean', 'SourceOriginalResidueHurwitz2018a.exit', 'SourceOriginalResidueHurwitz2018a.lean', 'SourceOriginalResidueHurwitz2018a.log', 'SourceOriginalTameGenusCriterion-2027.exit', 'SourceOriginalTameGenusCriterion-2027.log', 'SourceOriginalTameGenusCriterion.lean', 'SourceOriginalTameGenusCriterion2021a.exit', 'SourceOriginalTameGenusCriterion2021a.lean', 'SourceOriginalTameGenusCriterion2021a.log', 'SourceOriginalTameGenusLower-2027.exit', 'SourceOriginalTameGenusLower-2027.log', 'SourceOriginalTameGenusLower.lean', 'SourceOriginalTameGenusLower2022a.exit', 'SourceOriginalTameGenusLower2022a.lean', 'SourceOriginalTameGenusLower2022a.log', 'SourceOriginalWildGenusLower-2027.exit', 'SourceOriginalWildGenusLower-2027.log', 'SourceOriginalWildGenusLower.lean', 'SourceOriginalWildGenusLower2019a.exit', 'SourceOriginalWildGenusLower2019a.lean.txt', 'SourceOriginalWildGenusLower2019a.log', 'SourceOriginalWildGenusLower2019b.exit', 'SourceOriginalWildGenusLower2019b.lean.txt', 'SourceOriginalWildGenusLower2019b.log', 'SourceOriginalWildGenusLower2019c.exit', 'SourceOriginalWildGenusLower2019c.lean.txt', 'SourceOriginalWildGenusLower2019c.log', 'SourceOriginalWildGenusLower2019d.exit', 'SourceOriginalWildGenusLower2019d.lean.txt', 'SourceOriginalWildGenusLower2019d.log', 'SourceOriginalWildGenusLower2019e.exit', 'SourceOriginalWildGenusLower2019e.lean', 'SourceOriginalWildGenusLower2019e.log', 'audit_gammaone_genus_comparison_2014.ps1', 'audit_gammaone_geometric_consumers_2032.ps1', 'audit_gammaone_geometric_consumers_2032b.ps1', 'audit_original_genus_preservation_2027.ps1', 'build_gammaone_genus_comparison_canonical_2014.ps1', 'build_gammaone_geometric_consumers_canonical_2032.ps1', 'build_original_genus_preservation_canonical_2027.ps1', 'gammaone-genus-comparison-versions-2014.json', 'gammaone-geometric-consumers-versions-2032.json', 'original-genus-consumers-promotion-route-2037.json', 'original-genus-preservation-audit-selection-2027.json', 'original-genus-preservation-versions-2027.json', 'prepare_gammaone_genus_comparison_audit_2014.py', 'prepare_gammaone_geometric_consumers_audit_2032.py', 'prepare_original_genus_preservation_audit_2027.py', 'record_gammaone_genus_comparison_2014.py', 'record_gammaone_geometric_consumers_2032.py', 'record_gammaone_geometric_consumers_2032b.py', 'record_original_genus_preservation_2027.py', 'source-gammaone-genus-comparison-1-audit-config.json', 'source-gammaone-genus-comparison-1-reuse-review-20261116.json', 'source-gammaone-genus-comparison-1-scratch-receipt.json', 'source-gammaone-genus-comparison-audit-route-2014.json', 'source-gammaone-geometric-consumers-1-audit-config.json', 'source-gammaone-geometric-consumers-1-reuse-review-20261116.json', 'source-gammaone-geometric-consumers-1-scratch-receipt.json', 'source-gammaone-geometric-consumers-1b-audit-config.json', 'source-gammaone-geometric-consumers-audit-route-2032.json', 'source-original-genus-preservation-1-audit-config.json', 'source-original-genus-preservation-1-reuse-review-20261116.json', 'source-original-genus-preservation-1-scratch-receipt.json', 'source-original-genus-preservation-audit-route-2027.json']]
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
supplemental_review_path=r/archive_rel/'original-genus-consumers-promotion-route-2037.json'

audit = r / "Extension/Dubon2026/Audit.lean"
at = audit.read_text(encoding="utf-8")
for n in queries:
    assert not re.search(r"``" + re.escape(n) + r"(?=[,\s])", at)
tm, dm = "\n]\n\nprivate def publicConstructions", "\n]\n\nprivate def runAudit"
assert at.count(tm) == at.count(dm) == 1
at = at.replace(tm, "".join("\n  ,``" + n for n in theorems) + tm, 1)
at = at.replace(dm, "".join("\n  ," + chr(96)*2 + n for n in defs) + dm, 1)
research_path = r / "Tools/lean-reuse-audit-20261020.json"
reuse_path = r / "Tools/source-original-genus-consumers.json"
oldresearch = json.loads(research_path.read_text(encoding="utf-8"))
assert oldresearch["receipt9533"]["exit"] == 0 and not reuse_path.exists()
dependency = 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> automorphy -> original all-weight characteristic-zero association -> homogeneous Gamma1 Hecke-character realization -> original genus preservation and its actual Hecke and arithmetic descent consumers.'
discharged = 'For every nonzero original Gamma1 level and every residue prime away from it, including two and three, the literal residue-image genus equals the original arithmetic genus. Native arithmetic-to-complex comparison, all-characteristic separating-coordinate canonical duality and Hurwitz, actual wild and tame fiber contributions, and small-level index bounds discharge every genus premise. At the prescribed rational local valuations, both coordinate degree and genus preservation now supply the actual diamond quotient Hecke operators and arithmetic descent of the homogeneous-valued Tate action. The original quotient-character assembly retains only parabolic transfer alongside its unchanged prime range and exceptional integer.'
boundary = 'Parabolic transfer, exceptional-prime removal, two-dimensional characteristic-zero realization, original all-weight association, remaining local/image/regularity inputs, automorphy and literal higher symmetric-power continuation remain required. Acceptance stays 16/20; DUB-17--20 OPEN; every original source and verification criterion is unchanged.'
status = 'The 26-module scratch scope passes 46 public axiom queries, 110 exhaustive theorem checks, sixteen linters per module and three declaration-value audits with 75 required dependencies, with zero diagnostics. Production aggregate, focused audits and sequential foundation/paper verification of the 9,559-module scope are pending.'
route = 'Native conorm divisor spaces and separating-coordinate genus stabilization give the original arithmetic-to-complex comparison. Existing local generation, global trace and rational residue proofs extend canonical degree and Hurwitz to every characteristic using explicit separation. Original wild and tame bounds supply reverse genus; finite signed-index calculations settle levels one, two and three. Existing Frobenius, inertia and arithmetic descent consumers then discharge both geometric families without new representation or operator infrastructure. Three scratch scopes pass 75 proof-VALUE dependencies, exhaustive public/private/generated axiom checks and sixteen linters per module. The unused finite-set ramification variant is separately axiom checked and is not claimed as a VALUE dependency. The corrected consumer audit retains all thirteen required edges and fixes only one declaration namespace; its failed predecessor is preserved. Promotion changes imports only. Paper, root pins, proof limits and owner-only BAT are unchanged.'

dateLabel = datetime.now().strftime('%d %B %Y').lstrip('0')
note = ('Original Gamma1 genus preservation and its consumers (' + dateLabel + '): ' + discharged + ' Source dependency chain: ' + dependency + ' ' + boundary + ' ' + status + ' The preceding 9,533-module scope passed sequential canonical verification with zero diagnostics and all thirteen regressions. ' + route)
corrections = []
count = sum(z['exhaustiveTheorems'] for z in certs)
assert count == 110

docpaths = list(dict.fromkeys(r / rel for rel in c["statusDocuments"] + ["Dubon Remaining Obligations.md"]))
for f in docpaths:
    assert "\n\n" in f.read_text(encoding="utf-8")
readmes = [(r.parent / "README.md", "Current Project 83 status ("), (repo / "README.md", "Project 83 has an ")]
for f, prefix in readmes:
    assert sum(line.startswith(prefix) for line in f.read_text(encoding="utf-8").splitlines()) == 1
arch = r / "Dubon Architecture.md"
edge = '  WILDCENSUS9533["Actual original wild orders twelve/six and different contributions fourteen/seven proved for N greater than three. Canonical degree, Hurwitz, small levels, reverse genus and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
assert arch.read_text(encoding="utf-8").count(edge) == 1

for path in [p/'SourceOriginalGenusConsumersProductionAudit9559.lean',p/'source-original-genus-consumers-9559-production-audits.json']:
    assert not path.exists(),path
for cert in certs:
    target=p/(Path(cert['dependencyAuditLog']).stem+'Production9559.lean')
    assert not target.exists(),target

# Register the preceding canonical recorder's additional immutable evidence.
priorArchive = r / 'Tools/marked-wild-census-20261116-2007'
registered = {row['path'] for row in c['files']}
for priorFile in priorArchive.iterdir():
    rel = priorFile.relative_to(r).as_posix()
    if priorFile.is_file() and rel not in registered:
        c['files'].append({'path': rel, 'role': 'Tools'})

reportSource = p / 'Dubon Original Genus and Consumers Assessment 2026-11-16.md'
assert sha(reportSource) == 'A33B935DA221D4620DF7F839055B34F10CF47914F5E81342CF5D379ACA25982C'
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
    "productionModules": 9559, "modules": newmods, "queries": queries,
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
arch.write_text(arch.read_text(encoding='utf-8').replace(edge,'  WILDCENSUS9533["Actual original wild fiber orders and different contributions proved (DUB-17/18)"] --> GENUS9559\n  GENUS9559["Original Gamma1 genus preservation at every nonzero level and away residue prime proved; actual quotient Hecke operators and arithmetic descent have no geometric premises. Parabolic transfer, association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'),encoding='utf-8')



for f, prefix in readmes:
    lines = f.read_text(encoding="utf-8").splitlines(keepends=True)
    i = next(i for i, line in enumerate(lines) if line.startswith(prefix))
    intro = "Current Project 83 status (" + dateLabel + "): " if f.parent == r.parent else lines[i].split("). ", 1)[0] + "). "
    lines[i] = intro + note + "\n"
    f.write_text("".join(lines), encoding="utf-8")
f = r / 'Dubon Sources.md'
f.write_text(f.read_text(encoding='utf-8') + '\n## Original Gamma1 genus preservation and its consumers - ' + dateLabel + '\n\nThe [assembled proof record](Tools/source-original-genus-consumers.json) records ' + discharged + '\n\n' + route + '\n\n' + boundary + '\n',encoding='utf-8')

s = (p / "SourceResidueFunctionalAudit3.lean").read_text(encoding="utf-8")
b = s[s.index("private def runSourceResidueFunctionalAudit"):s.index("#eval runSourceResidueFunctionalAudit")]
for label, names in [("modules", newmods), ("theorems", theorems), ("constructions", defs)]:
    b = re.sub(r"  let " + label + r" : Array Name := #[^\n]+",
        "  let " + label + " : Array Name := #[" + ", ".join("`" + n for n in names) + "]", b)
b = re.sub('  logInfo m!".*"\n', '  logInfo m!"SOURCE ORIGINAL GENUS CONSUMERS AUDIT PASS: {count} theorems including private/generated declarations. Original all-level genus preservation, quotient Hecke operators and arithmetic descent proved. Parabolic transfer and source gates OPEN;16/20 gates."\n', b)
out = "".join("import " + m + "\n" for m in newmods) + "import Mathlib.Tactic\n\nopen Lean\n\n"
out += "".join("#print axioms " + q + "\n" for q in queries) + "\n" + b
out += "#eval runSourceResidueFunctionalAudit\n\n" + "\n".join("#lint in " + m + "\n" for m in newmods)
(p / "SourceOriginalGenusConsumersProductionAudit9559.lean").write_text(out, encoding="utf-8")
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
    target = p / (source.stem + "Production9559.lean")
    assert not target.exists()
    target.write_text(s, encoding="utf-8")
    audits.append(target.stem)
(p / "source-original-genus-consumers-9559-production-audits.json").write_text(json.dumps(audits, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"productionModules": 9559, "increment": 26, "queries": 46,
    "exhaustiveIncrement": count, "proofAudits": audits, "gates": "16/20", "productionVerification": "pending"}))
