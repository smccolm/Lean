from pathlib import Path
import ast, json, re, hashlib

p = Path(__file__).parent
r = Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
stems = [
    'source-gamma-one-analytic-integrality-3', 'source-gamma-one-finite-place-exhaustion-1',
    'source-gamma-one-place-invariance-2', 'source-period-division-rotations-1',
    'source-gamma-one-division-forms-1', 'source-gamma-one-division-lattice-orbit-1',
    'source-gamma-one-division-power-orbit-1', 'source-gamma-one-diamond-separation-1',
    'source-original-modular-point-separation-1', 'source-gamma-one-modular-point-separation-1',
    'source-gamma-one-normalized-cusp-ratios-1', 'source-gamma-one-all-modular-ratio-membership-1',
    'source-gamma-one-analytic-place-orbits-1', 'source-gamma-one-j-fiber-degree-1',
    'source-gamma-one-orbit-counting-1', 'source-gamma-one-plus-minus-1',
    'source-gamma-one-ramification-bounds-1', 'source-gamma-one-j-fiber-orbits-1',
    'source-gamma-one-generic-fiber-count-1']
names = [s + '-scratch-receipt.json' for s in stems]
certs = [json.loads((p / n).read_text(encoding='utf-8')) for n in names]
digests = {n: sha(p / n) for n in names}
assert len(certs) == 19
assert tuple(sum(len(c[k]) for c in certs) for k in
             ['modules', 'queries', 'theoremRegistrations', 'constructionRegistrations']) == (22, 62, 55, 7)
assert sum(c['exhaustiveTheorems'] for c in certs) == 94
assert sum(c['requiredProofValueEdges'] for c in certs) == 156
prior = json.loads((r / 'Tools/lean-reuse-audit-20261015.json').read_text(encoding='utf-8'))
assert prior['appliedSourceGammaOnePeriodCharts']['receipt8554']['exit'] == 0
assert (r / 'Tools/gamma-one-period-charts-20261026-709/canonical-evidence-8554.json').exists()

routefile = 'gamma-one-analytic-orbits-promotion-route-730.json'
archive = 'Tools/gamma-one-analytic-orbits-20261027-730'
dependency = ('DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation '
    '-> arithmetic automorphy -> original all-weight characteristic-zero association -> arithmetic realization '
    'of original finite Gamma1 Hecke characters -> Picard/H1, full/parabolic, transpose and diamond comparison '
    'retaining the original homogeneous coefficient endomorphism -> actual global differential/cusp period '
    'geometry -> exact analytic-place orbit identification and finite-fiber ramification comparison.')
discharged = ('Regularity at every actual analytic place implies integrality over the original complex j line, '
    'and every finite place is realized by an actual upper-half-plane point. Native complex Gamma1 modular forms '
    'separate distinct Gamma1 orbits at every nonzero level, including elliptic points; their literal Fourier '
    'ratios lie in the original integral-ratio function field by the proved integral cusp spanning theorem. '
    'Consequently two actual analytic places are equal exactly on one Gamma1 orbit. The actual positive j fiber '
    'is in bijection with the corresponding subgroup orbits, with exact transport of place-order sums. '
    'Every finite fiber has the same total order, equal to the actual coordinate extension degree, and one '
    'genuine generic fiber has total order equal to the subgroup index. Actual uniformizer invariance and '
    'j multiplicity give the termwise ramification bound and its exact equality condition, with the central '
    'negative identity and required factor of two retained. No orbit dictionary, field membership, finite-place '
    'exhaustion, fiber bijection or degree identity is supplied as a hypothesis.')
boundary = ('The fixed-degree and generic-fiber sums must still be composed with the termwise bounds to prove '
    'exact elliptic ramification. Global Gamma1 charts, cusp charts and actual global period and '
    'Hecke/diamond/Picard/H1 comparison remain. These results do not close the arithmetic realization of '
    'original finite homogeneous-coefficient characters. Coefficient-field transport, Frobenius/inertia, '
    'original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and '
    'literal higher symmetric-power continuation remain. The full all-weight arithmetic goal is unchanged. '
    'Complex semisimplicity, finite characters, Witt coefficients and universal deformation rings do not '
    'supply a characteristic-zero lift or point. 16/20; DUB-17--20 OPEN.')
route = ('The renewed Lean reuse search supplies selected pinned Apache-2.0 division-form, orbit and '
    'ramification arguments. Shorter local routes reuse the existing Gamma0 integral-closure centers, '
    'integral Gamma1 cusp spanning, actual analytic representatives, positive-place-order degree sum and '
    'analytic j-surjectivity. Native modular-form powers and finite orbit-stabilizer APIs are consumed. '
    'No external import closure, new coefficient field, repeated rational-function comparison framework '
    'or separate 2*i fundamental-domain calculation is introduced. Only audited mathematical sources are '
    'promoted and only imports are qualified. Failed variants, audit classifications and all predecessor '
    'evidence remain preserved. Pins, proof limits, frozen paper and all twenty acceptance gates are unchanged.')
status = ('Actual Gamma1 finite-place exhaustion, exact analytic-place orbits and finite j-fiber comparisons '
    'pass 94 exhaustive scratch theorem checks and 62 public axiom queries across 22 modules, with sixteen '
    'linters per module and zero diagnostics. Nineteen declaration-value audits verify 156 required '
    'dependencies. Production aggregate, focused audit and sequential foundation/paper verification '
    'of the 8,576-module scope are pending.')

def output(n, s):
    with (p / n).open('x', encoding='utf-8', newline='\n') as f:
        f.write(s)

output(routefile, json.dumps(dict(scope=730, scopeIds=[710, 711, 713, 714, 715, 716, 717, 718,
    719, 720, 721, 722, 723, 724, 725, 726, 727, 728, 729], receipts=digests, dependency=dependency,
    discharged=discharged, remaining=boundary, route=route, precedingCanonicalScope=8554,
    rootPinsChanged=False, proofLimitsChanged=False, externalImport=False,
    fullGoal='16/20; DUB-17--20 OPEN; all 20 gates unchanged.',
    reason='Preceding canonical PASS and immutable archive verified before preparing production mutation.'), indent=2) + '\n')

repl = {
    'gamma-one-period-charts-promotion-route-709.json': routefile,
    'Tools/gamma-one-period-charts-20261026-709': archive,
    'Tools/gamma-one-regular-cusp-20261026-704': 'Tools/gamma-one-period-charts-20261026-709',
    'appliedSourceGammaOnePeriodCharts': 'appliedSourceGammaOneAnalyticOrbits',
    'appliedSourceGammaOneRegularCusp': 'appliedSourceGammaOnePeriodCharts',
    'SourceGammaOnePeriodCharts': 'SourceGammaOneAnalyticOrbits',
    'gamma_one_period_charts': 'gamma_one_analytic_orbits',
    'source-gamma-one-period-charts': 'source-gamma-one-analytic-orbits',
    'SOURCE GAMMA ONE PERIOD CHARTS': 'SOURCE GAMMA ONE ANALYTIC ORBITS',
    'actual Gamma1 period normalization and local charts': 'actual Gamma1 analytic-place orbits and finite fibers',
    'Actual Gamma1 period normalization and local charts': 'Actual Gamma1 analytic-place orbits and finite fibers',
    '8,554': '8,576', '8,548': '8,554', '8554': '8576', '8548': '8554'}
rx = re.compile('|'.join(map(re.escape, sorted(repl, key=len, reverse=True))))
tr = lambda s: rx.sub(lambda m: repl[m[0]], s)
s = tr((p / 'integrate_source_gamma_one_period_charts_8554.py').read_text(encoding='utf-8'))
s = re.sub(r'^digests = .+$', lambda _: 'digests = ' + repr(digests), s, flags=re.M)
s = s.replace('(6, 6, 19, 18, 1)', '(22, 22, 62, 55, 7)').replace('count == 31', 'count == 94')
s = s.replace('"increment": 6, "queries": 19', '"increment": 22, "queries": 62')
for k, v in [('dependency', dependency), ('discharged', discharged), ('boundary', boundary),
             ('route', route), ('status', status)]:
    assert re.search(r'^' + k + r' = .+$', s, re.M), k
    s = re.sub(r'^' + k + r' = .+$', lambda _, k=k, v=v: k + ' = ' + repr(v), s, flags=re.M)

owners = ['SourceGammaOneAnalyticIntegralityScratchOwnership710',
    'SourceGammaOneFinitePlaceExhaustionScratchOwnership711',
    'SourceGammaOnePlaceInvarianceScratchOwnership713', 'SourcePeriodDivisionRotationsScratchOwnership714',
    'SourceGammaOneDivisionFormsScratchOwnership715', 'SourceGammaOneDivisionLatticeOrbitScratchOwnership716',
    'SourceGammaOneDivisionPowerOrbitScratchOwnership717', 'SourceGammaOneDiamondSeparationScratchOwnership718',
    'SourceOriginalModularPointSeparationScratchOwnership719', 'SourceGammaOneModularPointSeparationScratchOwnership720',
    'SourceGammaOneNormalizedCuspRatiosScratchOwnership721', 'SourceGammaOneAllModularRatioMembershipScratchOwnership722',
    'SourceGammaOneAnalyticPlaceOrbitsScratchOwnership723', 'SourceGammaOneJFiberDegreeScratchOwnership724',
    'SourceGammaOneOrbitCountingScratchOwnership725', 'SourceGammaOnePlusMinusScratchOwnership726',
    'SourceGammaOneRamificationBoundsScratchOwnership727', 'SourceGammaOneJFiberOrbitsScratchOwnership728',
    'SourceGammaOneGenericFiberCountScratchOwnership729']
evidence = list(names) + [stem + '-audit-config.json' for stem in stems]
evidence.append('source-gamma-one-plus-minus-1b-audit-config.json')
for cert in certs:
    for key in ['log', 'dependencyAuditLog']:
        f = Path(cert[key]); evidence += [f.with_suffix(ext).name for ext in ['.lean', '.log', '.exit']]
    for item in cert['files']:
        f = Path(item['path']); evidence += [f.with_suffix(ext).name for ext in ['.lean', '.log', '.exit']]
    review = json.loads(Path(cert['reuseReview']).read_text(encoding='utf-8'))
    evidence.append(Path(review['routeAssessment']['path']).name)
scopePattern = '(?:' + '|'.join(map(str, range(710, 730))) + ')'
for f in p.iterdir():
    if f.is_file() and f.suffix in ['.json', '.py', '.ps1', '.txt', '.log', '.exit'] and re.search(
            r'(?<!\d)' + scopePattern + r'[a-z]?(?:\.|-)', f.name):
        evidence.append(f.name)
for stem in owners:
    evidence += [stem + ext for ext in ['.lean', '.log', '.exit']]
folders = [f.name for f in p.iterdir() if f.is_dir() and re.search(scopePattern + r'[a-z]?$', f.name)]
for n in evidence + folders:
    assert (p / n).exists(), n
a = s.index('evidence=[p/'); b = s.index("for cert in certs:\n    evidence.append", a)
s = s[:a] + 'evidence=[p/' + repr(routefile) + ']\nevidence += [p/n for n in ' + repr(sorted(set(evidence))) + \
    ']\nfor folder in ' + repr(folders) + ':\n    evidence += sorted(f for f in (p/folder).rglob("*") if f.is_file())\n' + s[b:]
oldedge = '  GAMMAONEPERIOD8554["Exact differential integrand, actual residue comparison and unramified local charts proved. Elliptic/global charts, period/Hecke/diamond/Picard/H1, all-weight arithmetic association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
newedge = ('  GAMMAONEPERIOD8554["Exact differential integrand, actual residue comparison and unramified local charts (DUB-17/18)"] --> GAMMAONEORBITS8576\n'
    '  GAMMAONEORBITS8576["Actual Gamma1 finite-place exhaustion, exact analytic-place orbits and finite j-fiber bijections proved. Exact elliptic ramification/global charts, period/Hecke/diamond/Picard/H1, all-weight arithmetic association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538')
assert (r / 'Dubon Architecture.md').read_text(encoding='utf-8').count(oldedge) == 1
s = re.sub(r'^edge = .+$', lambda _: 'edge = ' + repr(oldedge), s, flags=re.M)
s = re.sub(r'^arch.write_text\(.*$', lambda _: "arch.write_text(arch.read_text(encoding='utf-8').replace(edge," + repr(newedge) + "),encoding='utf-8')", s, flags=re.M)
s = re.sub(r'^    "promotionChanges": .+$', lambda _: '    "promotionChanges": ' + repr(
    'Only scratch imports are qualified. All final audited statements, proof bodies and comments remain identical. '
    'Actual integral-ratio fields, native modular forms, literal Fourier series, analytic places and exact fiber multiplicities are retained. No source contract is weakened.') + ',', s, flags=re.M)
a = s.index("b = re.sub('  logInfo"); b = s.index(', b)', a) + len(', b)')
logline = ('  logInfo m!"SOURCE GAMMA ONE ANALYTIC ORBITS AUDIT PASS: {count} theorems including private/generated declarations. '
    'Actual finite-place exhaustion, exact Gamma1 analytic-place orbits, integral-ratio membership and finite j-fiber comparisons are proved. '
    'Composition to exact elliptic ramification and global chart/period obligations remains. Original Hecke/diamond/Picard/H1 arithmetic comparison remains; 16/20 gates."\n')
s = s[:a] + 'b = re.sub(' + repr('  logInfo m!".*"\n') + ', ' + repr(logline) + ', b)' + s[b:]
output('integrate_source_gamma_one_analytic_orbits_8576.py', s)
scripts = ['integrate_source_gamma_one_analytic_orbits_8576.py']
for stem in ['prepare_gamma_one_period_charts_production_ownership', 'prepare_gamma_one_period_charts_global_ownership']:
    n = tr(stem + '_8554.py'); output(n, tr((p / (stem + '_8554.py')).read_text(encoding='utf-8'))); scripts.append(n)
s = tr((p / 'compare_gamma_one_period_charts_ownership_8554.py').read_text(encoding='utf-8'))
s = s.replace('len(names)==len(certs)==3', 'len(names)==len(certs)==19').replace(
    'len(allmods)==len(set(allmods))==6', 'len(allmods)==len(set(allmods))==22').replace(
    "result['scratchSum']==31", "result['scratchSum']==94").replace('All 6 mathematical', 'All 22 mathematical')
n = 'compare_gamma_one_analytic_orbits_ownership_8576.py'; output(n, s); scripts.append(n)
s = tr((p / 'record_source_gamma_one_period_charts_8554.py').read_text(encoding='utf-8'))
s = re.sub(r'\b31\b', '94', s); s = re.sub(r'== 6\b', '== 22', s); s = re.sub(r'== 3\b', '== 19', s)
s = s.replace('"incrementModules": 6', '"incrementModules": 22').replace('"linterScopes": 6', '"linterScopes": 22')
s = s.replace('Three declaration-value audits verify 43 required dependencies.', 'Nineteen declaration-value audits verify 156 required dependencies.')
s = s.replace('int(a[2]) == 24737', 'int(a[2]) == 24792')
n = 'record_source_gamma_one_analytic_orbits_8576.py'; output(n, s); scripts.append(n)
for stem in ['verify_gamma_one_period_charts', 'build_gamma_one_period_charts']:
    n = tr(stem + '_8554.ps1'); output(n, tr((p / (stem + '_8554.ps1')).read_text(encoding='utf-8'))); scripts.append(n)
n = 'archive_gamma_one_analytic_orbits_canonical_8576.py'
output(n, tr((p / 'archive_gamma_one_period_charts_canonical_8554.py').read_text(encoding='utf-8'))); scripts.append(n)
output('source-gamma-one-analytic-orbits-scratch-ownership-8576.json', json.dumps(owners, indent=2) + '\n')
for n in scripts:
    if (p / n).suffix == '.py':
        ast.parse((p / n).read_text(encoding='utf-8'))
output('gamma-one-analytic-orbits-preexecution-review-8576.json', json.dumps(dict(
    status='Prepared; preceding 8554 canonical PASS and archive verified. Review before integration.',
    route=routefile, routeSha256=sha(p / routefile), modules=22, queries=62, theorems=55, constructions=7,
    exhaustiveScratchChecks=94, proofValueEdges=156, scopes=19, receipts=digests,
    expectedConsumers=24792, expectedConstructions=2464,
    fullGoal='16/20; DUB-17--20 OPEN; all 20 gates unchanged.',
    scripts=[dict(path=str(p / n), sha256=sha(p / n)) for n in scripts], productionMutation=False), indent=2) + '\n')
print(json.dumps(dict(scripts=len(scripts), modules=22, checks=94,
    archivedFailureAndReuseFolders=len(folders), productionMutation=False)))
