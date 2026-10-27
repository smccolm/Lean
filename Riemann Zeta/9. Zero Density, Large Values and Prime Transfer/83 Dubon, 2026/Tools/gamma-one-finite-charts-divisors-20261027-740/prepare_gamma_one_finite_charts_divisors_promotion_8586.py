from pathlib import Path
import ast, json, re, hashlib

p = Path(__file__).parent
r = Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
stems = ['source-gamma-one-exact-ramification-1', 'source-gamma-one-ramified-regular-1b',
    'source-gamma-one-ramified-chart-orders-1b', 'source-gamma-one-finite-chart-parameters-1', 'source-gamma-one-divisor-moving-1']
names = [s + '-scratch-receipt.json' for s in stems]
certs = [json.loads((p / n).read_text(encoding='utf-8')) for n in names]
digests = {n: sha(p / n) for n in names}
assert len(certs) == 5
assert tuple(sum(len(c[k]) for c in certs) for k in
    ['modules', 'queries', 'theoremRegistrations', 'constructionRegistrations']) == (10, 22, 21, 1)
assert sum(c['exhaustiveTheorems'] for c in certs) == 48
assert sum(c['requiredProofValueEdges'] for c in certs) == 55
prior = json.loads((r / 'Tools/lean-reuse-audit-20261015.json').read_text(encoding='utf-8'))
assert prior['appliedSourceGammaOneAnalyticOrbits']['receipt8576']['exit'] == 0
assert (r / 'Tools/gamma-one-analytic-orbits-20261027-730/canonical-evidence-8576.json').exists()
assert sha(p / 'reuse-head-refresh-741/assessment.json') == '6E25C050F739B99FAFA2BD2928F1CD82E021169F95B5BFEAA2970CCF8A3D62B5'
assert sha(p / 'reuse-head-refresh-741/Dubon Reuse Refresh 2026-10-27.md') == '0492A53D656A52E89B93B5EB506066901BAB9507AF71E81608B394B1A338C34D'

routefile = 'gamma-one-finite-charts-divisors-promotion-route-740.json'
archive = 'Tools/gamma-one-finite-charts-divisors-20261027-740'
dependency = ('DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation '
    '-> arithmetic automorphy -> original all-weight characteristic-zero association -> arithmetic realization '
    'of original finite Gamma1 Hecke characters -> Picard/H1, full/parabolic, transpose and diamond comparison '
    'retaining the original homogeneous coefficient endomorphism -> actual differential and period geometry '
    '-> exact normalized charts at all finite places, including elliptic points, and analytic representatives ' 
    'of all original degree-zero divisor classes.')
discharged = ('The actual coordinate extension degree equals the index of Gamma1 enlarged by the central '
    'negative identity. Equality of finite-fiber sums with the termwise bounds proves twice the actual '
    'analytic ramification equals the actual enlarged stabilizer cardinality. Actual places are constant '
    'on centered-coordinate power fibers, so regular residue values descend analytically with their exact '
    'normalized orders. Inversion extends the result to all meromorphic functions. One disk works for '
    'every function and every nearby point. Every actual place where j is regular has an injective '
    'uniformizer-normalized chart, exact function orders, regular analyticity and coordinate differences '
    'of order one. Every nonzero level and elliptic center is retained. No ramification equality, normalized '
    'finite chart, analytic descent or function-order comparison remains a supplied hypothesis. ' 
    'Actual finite-place indicators prescribe arbitrary orders without an approximation input. Subtracting ' 
    'the resulting principal divisor moves every actual divisor class to a finite analytic divisor; ' 
    'degree-zero classes have analytic coefficient sum zero.')
boundary = ('Actual global period and Hecke/diamond/Picard/H1 comparison remain. Cusp/global-chart '
    'construction and a possible modular-period alternative are being compared; the pinned alternative '
    'still requires genuine period surjectivity, reciprocity, meromorphic field realization and cusp-order '
    'control. The present results do not close arithmetic realization of original finite homogeneous-coefficient '
    'characters. Coefficient-field transport, Frobenius/inertia, original all-weight characteristic-zero '
    'association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation '
    'remain. The full all-weight arithmetic goal is unchanged. Complex semisimplicity, finite characters, '
    'Witt coefficients and universal deformation rings do not supply a characteristic-zero lift or point. '
    '16/20; DUB-17--20 OPEN.')
route = ('Selected pinned Apache-2.0 elliptic and ramified-chart arguments are adapted using already proved '
    'local exact fiber counts, native power descent, local root branches, rational residue inversion and the '
    'existing inverse-function parameter theorem. Actual curve geometry and finite-place indicators supply ' 
    'the required divisor-moving argument. This avoids rebuilding those foundations. The renewed '
    'search also identifies an alternative principal-divisor proof using nonzero cusp limits; its full '
    'dependencies are under assessment in the preserved scope-736 and scope-739 research and are not claimed proved. '
    'The live 27 October refresh of seven repositories and the inspected new Mathlib, OpenAI and zeta-lab changes '
    'are recorded in [Dubon Reuse Refresh 2026-10-27.md](Dubon%20Reuse%20Refresh%202026-10-27.md); '
    'none of the inspected updates closes the missing arithmetic or global-period obligation. '
    'Only audited mathematical sources are promoted, with imports qualified and proof bodies unchanged. '
    'The unused-argument correction, completed predecessor checks and every failure are preserved. '
    'Pins, proof limits, frozen paper and all twenty acceptance gates are unchanged.')
status = ('Actual Gamma1 exact elliptic ramification and normalized charts at every finite j-place '
    'and analytic divisor representatives pass 48 exhaustive scratch theorem checks and 22 public axiom queries across ten modules, with '
    'sixteen linters per module and zero diagnostics. Five declaration-value audits verify 55 required '
    'dependencies. Production aggregate, focused audit and sequential foundation/paper verification '
    'of the 8,586-module scope are pending.')

def output(n, s):
    with (p / n).open('x', encoding='utf-8', newline='\n') as f:
        f.write(s)

output(routefile, json.dumps(dict(scope=740, scopeIds=[731, 732, 733, 734, 735, 738], researchScopes=[736, 739, 741],
    receipts=digests, dependency=dependency, discharged=discharged, remaining=boundary, route=route,
    precedingCanonicalScope=8576, rootPinsChanged=False, proofLimitsChanged=False, externalImport=False,
    fullGoal='16/20; DUB-17--20 OPEN; all 20 gates unchanged.',
    reason='Preceding canonical PASS and immutable archive verified before preparing production mutation.'), indent=2) + '\n')

repl = {
    'gamma-one-analytic-orbits-promotion-route-730.json': routefile,
    'Tools/gamma-one-analytic-orbits-20261027-730': archive,
    'Tools/gamma-one-period-charts-20261026-709': 'Tools/gamma-one-analytic-orbits-20261027-730',
    'appliedSourceGammaOneAnalyticOrbits': 'appliedSourceGammaOneFiniteChartsDivisors',
    'appliedSourceGammaOnePeriodCharts': 'appliedSourceGammaOneAnalyticOrbits',
    'SourceGammaOneAnalyticOrbits': 'SourceGammaOneFiniteChartsDivisors',
    'gamma_one_analytic_orbits': 'gamma_one_finite_charts_divisors',
    'source-gamma-one-analytic-orbits': 'source-gamma-one-finite-charts-divisors',
    'SOURCE GAMMA ONE ANALYTIC ORBITS': 'SOURCE GAMMA ONE FINITE CHARTS AND DIVISORS',
    'actual Gamma1 analytic-place orbits and finite fibers': 'actual Gamma1 finite charts and analytic divisor representatives',
    'Actual Gamma1 analytic-place orbits and finite fibers': 'Actual Gamma1 finite charts and analytic divisor representatives',
    '8,576': '8,586', '8,554': '8,576', '8576': '8586', '8554': '8576'}
rx = re.compile('|'.join(map(re.escape, sorted(repl, key=len, reverse=True))))
tr = lambda s: rx.sub(lambda m: repl[m[0]], s)
s = tr((p / 'integrate_source_gamma_one_analytic_orbits_8576.py').read_text(encoding='utf-8'))
s = re.sub(r'^digests = .+$', lambda _: 'digests = ' + repr(digests), s, flags=re.M)
s = s.replace('(22, 22, 62, 55, 7)', '(10, 10, 22, 21, 1)').replace('count == 94', 'count == 48')
s = s.replace('"increment": 22, "queries": 62', '"increment": 10, "queries": 22')
for k, v in [('dependency', dependency), ('discharged', discharged), ('boundary', boundary),
             ('route', route), ('status', status)]:
    assert re.search(r'^' + k + r' = .+$', s, re.M), k
    s = re.sub(r'^' + k + r' = .+$', lambda _, k=k, v=v: k + ' = ' + repr(v), s, flags=re.M)
owners = ['SourceGammaOneExactRamificationScratchOwnership731',
    'SourceGammaOneRamifiedRegularScratchOwnership733b',
    'SourceGammaOneRamifiedChartOrdersScratchOwnership734b',
    'SourceGammaOneFiniteChartParametersScratchOwnership735', 'SourceGammaOneDivisorMovingScratchOwnership738']
evidence = ['prepare_gamma_one_ramified_finite_charts_promotion_8584.py'] + list(names) + [stem + '-audit-config.json' for stem in stems]
for cert in certs:
    for key in ['log', 'dependencyAuditLog']:
        f = Path(cert[key]); evidence += [f.with_suffix(ext).name for ext in ['.lean', '.log', '.exit']]
    for item in cert['files']:
        f = Path(item['path']); evidence += [f.with_suffix(ext).name for ext in ['.lean', '.log', '.exit']]
    review = json.loads(Path(cert['reuseReview']).read_text(encoding='utf-8'))
    evidence.append(Path(review['routeAssessment']['path']).name)
scopePattern = '(?:731|732|733|734|735|736|738|739|741)'
for f in p.iterdir():
    if f.is_file() and f.suffix in ['.json', '.py', '.ps1', '.txt', '.log', '.exit'] and re.search(
            r'(?<!\d)' + scopePattern + r'[a-z]?(?:\.|-)', f.name):
        evidence.append(f.name)
for stem in owners:
    evidence += [stem + ext for ext in ['.lean', '.log', '.exit']]
# Preserve the earlier failed/passed audit variants as completed historical evidence.
for stem in ['SourceGammaOneRamifiedRegularAudit1', 'SourceGammaOneRamifiedRegularDependencyAudit1',
        'SourceGammaOneRamifiedChartOrdersAudit1', 'SourceGammaOneRamifiedChartOrdersDependencyAudit1',
        'SourceGammaOneRamifiedChartOrdersScratchOwnership734']:
    evidence += [stem + ext for ext in ['.lean', '.log', '.exit'] if (p / (stem + ext)).exists()]
for stem in ['source-gamma-one-ramified-regular-1', 'source-gamma-one-ramified-chart-orders-1']:
    evidence += [stem + ext for ext in ['-audit-config.json', '-scratch-receipt.json']
        if (p / (stem + ext)).exists()]
folders = [f.name for f in p.iterdir() if f.is_dir() and re.search(scopePattern + r'[a-z]?$', f.name)]
for n in evidence + folders:
    assert (p / n).exists(), n
a = s.index('evidence=[p/'); b = s.index("for cert in certs:\n    evidence.append", a)
s = s[:a] + 'evidence=[p/' + repr(routefile) + ']\nevidence += [p/n for n in ' + repr(sorted(set(evidence))) + \
    ']\nfor folder in ' + repr(folders) + ':\n    evidence += sorted(f for f in (p/folder).rglob("*") if f.is_file())\n' + s[b:]
oldedge = '  GAMMAONEORBITS8576["Actual Gamma1 finite-place exhaustion, exact analytic-place orbits and finite j-fiber bijections proved. Exact elliptic ramification/global charts, period/Hecke/diamond/Picard/H1, all-weight arithmetic association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538'
newedge = ('  GAMMAONEORBITS8576["Actual Gamma1 finite-place exhaustion, exact analytic-place orbits and finite j-fiber bijections (DUB-17/18)"] --> GAMMAONEFINITE8586\n'
    '  GAMMAONEFINITE8586["Exact elliptic ramification, normalized finite charts and analytic representatives of every divisor class proved. Global periods, Hecke/diamond/Picard/H1, all-weight arithmetic association and higher continuation OPEN (DUB-17/18)"] --> CMARITH4538')
assert (r / 'Dubon Architecture.md').read_text(encoding='utf-8').count(oldedge) == 1
s = re.sub(r'^edge = .+$', lambda _: 'edge = ' + repr(oldedge), s, flags=re.M)
s = re.sub(r'^arch.write_text\(.*$', lambda _: "arch.write_text(arch.read_text(encoding='utf-8').replace(edge," + repr(newedge) + "),encoding='utf-8')", s, flags=re.M)
s = re.sub(r'^    "promotionChanges": .+$', lambda _: '    "promotionChanges": ' + repr(
    'Only scratch imports are qualified. All final audited statements, proof bodies and comments remain identical. '
    'The actual original integral-ratio field, all nonzero levels, elliptic stabilizers, residue values and normalized place orders are retained.') + ',', s, flags=re.M)
a = s.index("b = re.sub('  logInfo"); b = s.index(', b)', a) + len(', b)')
logline = ('  logInfo m!"SOURCE GAMMA ONE FINITE CHARTS AND DIVISORS AUDIT PASS: {count} theorems including private/generated declarations. '
    'Exact elliptic ramification, normalized finite charts and analytic representatives of every divisor class are proved. '
    'Global periods and original Hecke/diamond/Picard/H1 arithmetic comparison remain; 16/20 gates."\n')
s = s[:a] + 'b = re.sub(' + repr('  logInfo m!".*"\n') + ', ' + repr(logline) + ', b)' + s[b:]
research_insert = '''reportSource = p / 'reuse-head-refresh-741/Dubon Reuse Refresh 2026-10-27.md'
assert sha(reportSource) == '0492A53D656A52E89B93B5EB506066901BAB9507AF71E81608B394B1A338C34D'
reportTarget = r / reportSource.name
assert not reportTarget.exists()
reportTarget.write_bytes(reportSource.read_bytes())
c['files'].append({'path': reportTarget.name, 'role': 'Research'})
'''
assert s.count('cp.write_text(') == 1
s = s.replace('cp.write_text(', research_insert + 'cp.write_text(', 1)
output('integrate_source_gamma_one_finite_charts_divisors_8586.py', s)
scripts = ['integrate_source_gamma_one_finite_charts_divisors_8586.py']
for stem in ['prepare_gamma_one_analytic_orbits_production_ownership', 'prepare_gamma_one_analytic_orbits_global_ownership']:
    n = tr(stem + '_8576.py'); output(n, tr((p / (stem + '_8576.py')).read_text(encoding='utf-8'))); scripts.append(n)
s = tr((p / 'compare_gamma_one_analytic_orbits_ownership_8576.py').read_text(encoding='utf-8'))
s = s.replace('len(names)==len(certs)==19', 'len(names)==len(certs)==5').replace(
    'len(allmods)==len(set(allmods))==22', 'len(allmods)==len(set(allmods))==10').replace(
    "result['scratchSum']==94", "result['scratchSum']==48").replace('All 22 mathematical', 'All 10 mathematical')
n = 'compare_gamma_one_finite_charts_divisors_ownership_8586.py'; output(n, s); scripts.append(n)
s = tr((p / 'record_source_gamma_one_analytic_orbits_8576.py').read_text(encoding='utf-8'))
s = re.sub(r'\b94\b', '48', s); s = re.sub(r'== 22\b', '== 10', s); s = re.sub(r'== 19\b', '== 5', s)
s = s.replace('"incrementModules": 22', '"incrementModules": 10').replace('"linterScopes": 22', '"linterScopes": 10')
s = s.replace('Nineteen declaration-value audits verify 156 required dependencies.', 'Five declaration-value audits verify 55 required dependencies.')
s = s.replace('int(a[2]) == 24792', 'int(a[2]) == 24813')
n = 'record_source_gamma_one_finite_charts_divisors_8586.py'; output(n, s); scripts.append(n)
for stem in ['verify_gamma_one_analytic_orbits', 'build_gamma_one_analytic_orbits']:
    n = tr(stem + '_8576.ps1'); output(n, tr((p / (stem + '_8576.ps1')).read_text(encoding='utf-8'))); scripts.append(n)
n = 'archive_gamma_one_finite_charts_divisors_canonical_8586.py'
output(n, tr((p / 'archive_gamma_one_analytic_orbits_canonical_8576.py').read_text(encoding='utf-8'))); scripts.append(n)
output('source-gamma-one-finite-charts-divisors-scratch-ownership-8586.json', json.dumps(owners, indent=2) + '\n')
for n in scripts:
    if (p / n).suffix == '.py':
        ast.parse((p / n).read_text(encoding='utf-8'))
output('gamma-one-finite-charts-divisors-preexecution-review-8586.json', json.dumps(dict(
    status='Prepared; preceding 8576 canonical PASS and archive verified. Review before integration.',
    route=routefile, routeSha256=sha(p / routefile), modules=10, queries=22, theorems=21, constructions=1,
    exhaustiveScratchChecks=48, proofValueEdges=55, scopes=5, receipts=digests,
    expectedConsumers=24813, expectedConstructions=2465,
    fullGoal='16/20; DUB-17--20 OPEN; all 20 gates unchanged.',
    scripts=[dict(path=str(p / n), sha256=sha(p / n)) for n in scripts], productionMutation=False), indent=2) + '\n')
print(json.dumps(dict(scripts=len(scripts), modules=10, checks=48,
    archivedFailureAndReuseFolders=len(folders), productionMutation=False)))
