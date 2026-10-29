from pathlib import Path
from datetime import datetime, timezone
import ast, hashlib, json, re

p = Path(__file__).parent
repo = Path(r'E:\Lean\Riemann Zeta')
src = repo / '9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026/Extension/Dubon2026'
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
versions = ['SourceMarkedChartPlaceOrbits1954b', 'SourceMarkedOriginalOfJChart1955e', 'SourceMarkedOriginalPlaceChart1956a', 'SourceMarkedFullTorsionNonempty1957c', 'SourceMarkedChartFiberSurjection1958b', 'SourceMarkedOriginalFiberChart1959a']
mapping = {v: re.sub(r'\d+[a-z]$', '', v) for v in versions}
modules = list(mapping.values())
base = 'Dubon2026.SourceFunctionField.'
mc, ta = base + 'MarkedChart.', base + 'MarkedTorsion.'
queries, files, theorems, constructions = [], [], [], []

def output(name, text):
    f = p / name
    assert not f.exists(), f
    if name.endswith('.py'):
        ast.parse(text)
    f.write_text(text, encoding='utf-8')

for v, m in mapping.items():
    f = p / (v + '.lean')
    assert f.with_suffix('.exit').read_text().strip() == '0'
    assert f.with_suffix('.log').stat().st_size == 0
    assert not (src / (m + '.lean')).exists()
    t = f.read_text(encoding='utf-8')
    ns = ta if m.startswith('SourceMarkedTorsion') else mc
    qs = re.findall(r'(?m)^(?:@\[[^]]*\] )?(theorem|lemma|def|abbrev)\s+(\S+)', t)
    queries += [ns + n for k, n in qs]
    theorems += [ns + n for k, n in qs if k in ['theorem', 'lemma']]
    constructions += [ns + n for k, n in qs if k in ['def', 'abbrev']]
    c = re.sub(r'(?m)^import (\S+)$', lambda x: 'import ' + mapping.get(x[1], x[1]), t)
    assert re.sub(r'(?m)^import .*\n', '', c) == re.sub(r'(?m)^import .*\n', '', t)
    output(m + '.lean', c)
    files.append(dict(version=v, module=m, sourcePath=str(f), originalSha256=sha(f), canonicalSha256=sha(p / (m + '.lean')), mathematicalBodyIdentical=True))
assert len(queries) == len(set(queries)) == 6
roots = [mc + 'exists_original_marked_fiber_chart']
edges = queries + [mc + n for n in ['exists_original_natural_marked_chart_full_torsion', 'exists_original_natural_marked_chart_algebraic', 'natural_marked_chart_surjective_of_normal']]
edges += ['Dubon2026.SourceCurve.Place.restrictAlongFinite_eq_iff_inertia', 'Dubon2026.SourceCurve.Place.exists_coordinate_embedding_restrict_eq', 'Dubon2026.SourceCurve.finite_galois_along_coordinate', 'Dubon2026.SourceEllipticVelu.nonempty_cyclic_subgroups_of_full_torsion', 'WeierstrassCurve.ofJ_j', 'RatFunc.transcendental_X', 'RatFunc.adjoin_X', 'isAddCyclic_iff_exists_addOrderOf_eq_natCard']

assert len(edges) == len(set(edges))
cfg = dict(modules=modules, theorems=theorems, constructions=constructions, queries=queries, roots=roots, proofEdges=edges, compileEvidence={m: m + '-1960' for m in modules}, separatelyAxiomChecked=[])
output('source-marked-fiber-chart-1-audit-config.json', json.dumps(cfg, indent=2) + '\n')
output('marked-fiber-chart-versions-1960.json', json.dumps(files, indent=2) + '\n')
imports = '\n'.join('import ' + m for m in modules) + '\nimport Mathlib.Tactic\n\nopen Lean\n\n'
def replace_array(t, name, names):
    arr = '#[' + ', '.join('`' + n for n in names) + ']'
    t, count = re.subn(r'(?m)^  let ' + name + r' : Array Name := #\[.*$', '  let ' + name + ' : Array Name := ' + arr, t)
    assert count == 1, name
    return t
upstream = []
for fn in ['source-integral-toric-forms-2-audit-config.json', 'source-original-toric-coordinates-3-audit-config.json', 'source-toric-marked-point-1-audit-config.json', 'source-marked-chart-construction-1-audit-config.json', 'source-marked-chart-stabilizer-2-audit-config.json', 'source-marked-natural-chart-1-audit-config.json', 'source-marked-algebraic-chart-1-audit-config.json']:
    upstream += json.loads((p / fn).read_text(encoding='utf-8'))['modules']
for old, new in [('SourceToricMarkedPointAudit1', 'SourceMarkedFiberChartAudit1'), ('SourceToricMarkedPointDependencyAudit1', 'SourceMarkedFiberChartDependencyAudit1'), ('SourceToricMarkedPointScratchOwnership1899', 'SourceMarkedFiberChartScratchOwnership1960')]:
    t = (p / (old + '.lean')).read_text(encoding='utf-8')
    t = t[t.index('private def'):]
    t = t.replace('ToricMarkedPoint', 'MarkedFiberChart').replace('Toric marked point', 'Marked algebraic chart').replace('SOURCE TORIC MARKED POINT', 'SOURCE MARKED FIBER CHART')
    if 'Dependency' in old:
        for n, ns in [('roots', roots), ('localModules', modules + upstream), ('required', edges)]:
            t = replace_array(t, n, ns)
        a, b = t.index('  logInfo m!'), t.index('\n\n#eval')
        t = t[:a] + '  logInfo m!"SOURCE MARKED FIBER CHART DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the VALUE closure of the actual original Gamma1 finite-j-fiber chart. The ofJ model discharges generic-j and base-field-generation assumptions. Normal chart exhaustion and native place lifting prove fiber surjectivity. The native inertia theorem identifies equal places exactly with signed inertia orbits. The full-torsion count supplies a marked point. Original diamond covariance is exact. Finite elliptic cardinal bounds and reverse genus remain open; DUB17--20 OPEN."' + t[b:]

    elif 'Ownership' in old:
        t = replace_array(t, 'mods', modules)
    else:
        t = t[:t.index('\n#lint')]
        for n, ns in [('modules', modules), ('theorems', theorems), ('constructions', constructions)]:
            t = replace_array(t, n, ns)
        t = '\n'.join('#print axioms ' + n for n in queries) + '\n\n' + t + '\n' + '\n'.join('#lint in ' + m for m in modules) + '\n'
    output(new + '.lean', imports + t)
reuse = ['SourceRationalCoordinatePlaceOrbits', 'SourceRationalCoordinateFiberSurjectivity', 'SourceEllipticFullTorsionNonemptyCyclic', 'SourceEllipticPrescribedFullInertiaImage', 'SourceEllipticCharTwoFullInertiaImage', 'SourceEllipticCharThreeFullInertiaImage']
paths = [src / (n + '.lean') for n in reuse]
route = dict(recordedUTC=datetime.now(timezone.utc).isoformat(),
 chain='DUB17 Theorem2.6 / DUB18 Cor8.2 -> literal higher symmetric-power continuation -> automorphy -> original all-weight characteristic-zero association -> homogeneous Gamma1 Hecke-character realization -> original genus preservation -> reverse genus -> finite elliptic residue fibers -> actual original-field marked-fiber chart.',
 shorterRoute='Use the actual finite Galois torsion field of the ofJ(X) curve over RatFunc K. Reuse native normalized embedding exhaustion and finite-place lifting instead of another coordinate presentation. Reuse the native inertia/restriction theorem for exact equality of original Gamma1 places. Existing prescribed specialization constructions supply the upstream finite field, full torsion and positive-order place in every characteristic.',
 assumptionsToDischarge=['ofJ_j, transcendental_X and adjoin_X discharge the generic-j and generated-base-field inputs.', 'The actual full-torsion cardinal supplies a point of exact order N.', 'Normalized-embedding exhaustion discharges the coverage assumption in the place-lifting consumer.', 'Native finite-place inertia conjugacy discharges the place-equality classification.', 'Original diamond embedding covariance implies original diamond covariance of actual places.'],
 remaining='Connect the native prescribed full-inertia specialization data and derive finite elliptic cardinal bounds, then reverse genus and the remaining original association and higher continuation. Acceptance16/20; DUB17--20 OPEN.',
 boundary='Six focused modules compile; exhaustive audit, promotion and assembled verification pending. The final chart is surjective on the original finite j fiber and its equality relation is exactly actual inertia transport up to sign. Its finite Galois field, N-squared torsion and positive-order inputs are explicit native upstream data.',
 reuseChecked=[dict(path=str(f), sha256=sha(f)) for f in paths])
output('source-marked-fiber-chart-audit-route-1960.json', json.dumps(route, indent=2) + '\n')

t = (p / 'build_toric_marked_point_canonical_1899.ps1').read_text(encoding='utf-8')
t = re.sub(r'(?m)^\$names=@\(.*$', '$names=@(' + ','.join("'" + m + "'" for m in modules) + ')', t).replace('1899', '1960').replace('toric_marked_point', 'marked_fiber_chart')
output('build_marked_fiber_chart_canonical_1960.ps1', t)
replacements = {'SourceToricMarkedPointAudit1': 'SourceMarkedFiberChartAudit1', 'SourceToricMarkedPointDependencyAudit1': 'SourceMarkedFiberChartDependencyAudit1', 'SourceToricMarkedPointScratchOwnership1899': 'SourceMarkedFiberChartScratchOwnership1960', 'record_toric_marked_point_1899': 'record_marked_fiber_chart_1960'}
t = (p / 'audit_toric_marked_point_1899.ps1').read_text(encoding='utf-8')
for a, b in replacements.items(): t = t.replace(a, b)
output('audit_marked_fiber_chart_1960.ps1', t)
t = (p / 'record_toric_marked_point_1899.py').read_text(encoding='utf-8')
replacements.update({'source-toric-marked-point-1': 'source-marked-fiber-chart-1', 'source-toric-marked-point-audit-route-1899': 'source-marked-fiber-chart-audit-route-1960', 'SOURCE TORIC MARKED POINT': 'SOURCE MARKED FIBER CHART', '(15, 66, 73)': str((len(modules), len(queries), len(edges))), '== 15': '== 6', 'linterScopes=15': 'linterScopes=6', 'all 73 required': 'all ' + str(len(edges)) + ' required', 'requiredProofValueEdges=73': 'requiredProofValueEdges=' + str(len(edges)), 'modules=15, queries=66': 'modules=6, queries=6', 'proofEdges=73': 'proofEdges=' + str(len(edges))})
for a, b in replacements.items(): t = t.replace(a, b)
output('record_marked_fiber_chart_1960.py', t)
print(json.dumps(dict(modules=len(modules), queries=len(queries), proofEdges=len(edges))))
