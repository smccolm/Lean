from pathlib import Path
from datetime import datetime, timezone
import ast, hashlib, json, re

p = Path(__file__).parent
repo = Path(r'E:\Lean\Riemann Zeta')
src = repo / '9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026/Extension/Dubon2026'
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
versions = ['SourceMarkedOriginalSeparability1944b', 'SourceMarkedSeparableChartValues1945b', 'SourceMarkedSeparableEmbeddingDescent1946b', 'SourceMarkedRationalPointDescent1947b', 'SourceMarkedOriginalAlgebraicChart1948d', 'SourceMarkedFullTorsionPointLift1949a', 'SourceMarkedChartNormalExhaustion1951a', 'SourceMarkedOriginalFullTorsionChart1952a']
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
assert len(queries) == len(set(queries)) == 8
roots = [mc + 'exists_original_natural_marked_chart_full_torsion']
edges = queries + [mc + n for n in ['exists_original_natural_marked_chart_generic', 'exists_original_marked_chart_stabilizer_equality', 'exists_normalized_embedding_conjugacy', 'original_coordinate_finite']]
edges += ['Dubon2026.SourceCurve.isSeparable_of_forall_pow_ne', 'Dubon2026.SourceFunctionField.pow_ne_jqModC', 'Dubon2026.SourceEllipticVelu.separable_root_mem_range_of_fixed', 'Dubon2026.SourceEllipticReduction.torsion_mem_specialization_range', 'IsAlgClosure.equivOfEquiv', 'IsAlgClosure.equivOfEquiv_algebraMap']
assert len(edges) == len(set(edges))
cfg = dict(modules=modules, theorems=theorems, constructions=constructions, queries=queries, roots=roots, proofEdges=edges, compileEvidence={m: m + '-1953' for m in modules}, separatelyAxiomChecked=[])
output('source-marked-algebraic-chart-1-audit-config.json', json.dumps(cfg, indent=2) + '\n')
output('marked-algebraic-chart-versions-1953.json', json.dumps(files, indent=2) + '\n')
imports = '\n'.join('import ' + m for m in modules) + '\nimport Mathlib.Tactic\n\nopen Lean\n\n'
def replace_array(t, name, names):
    arr = '#[' + ', '.join('`' + n for n in names) + ']'
    t, count = re.subn(r'(?m)^  let ' + name + r' : Array Name := #\[.*$', '  let ' + name + ' : Array Name := ' + arr, t)
    assert count == 1, name
    return t
upstream = []
for fn in ['source-integral-toric-forms-2-audit-config.json', 'source-original-toric-coordinates-3-audit-config.json', 'source-toric-marked-point-1-audit-config.json', 'source-marked-chart-construction-1-audit-config.json', 'source-marked-chart-stabilizer-2-audit-config.json', 'source-marked-natural-chart-1-audit-config.json']:
    upstream += json.loads((p / fn).read_text(encoding='utf-8'))['modules']
for old, new in [('SourceToricMarkedPointAudit1', 'SourceMarkedAlgebraicChartAudit1'), ('SourceToricMarkedPointDependencyAudit1', 'SourceMarkedAlgebraicChartDependencyAudit1'), ('SourceToricMarkedPointScratchOwnership1899', 'SourceMarkedAlgebraicChartScratchOwnership1953')]:
    t = (p / (old + '.lean')).read_text(encoding='utf-8')
    t = t[t.index('private def'):]
    t = t.replace('ToricMarkedPoint', 'MarkedAlgebraicChart').replace('Toric marked point', 'Marked algebraic chart').replace('SOURCE TORIC MARKED POINT', 'SOURCE MARKED ALGEBRAIC CHART')
    if 'Dependency' in old:
        for n, ns in [('roots', roots), ('localModules', modules + upstream), ('required', edges)]:
            t = replace_array(t, n, ns)
        a, b = t.index('  logInfo m!'), t.index('\n\n#eval')
        t = t[:a] + '  logInfo m!"SOURCE MARKED ALGEBRAIC CHART DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the VALUE closure of the actual original-field natural chart in the normal full-torsion field. Original-coordinate separability, Galois covariance and native fixed-root descent give the algebraic-target chart. Native full-torsion lifting supplies an exact-order point; normalized-embedding conjugacy proves exhaustion. The actual finite Galois source field discharges the algebraic and normal assumptions. Finite elliptic place-fiber bounds and reverse genus remain open; DUB17--20 OPEN."' + t[b:]
    elif 'Ownership' in old:
        t = replace_array(t, 'mods', modules)
    else:
        t = t[:t.index('\n#lint')]
        for n, ns in [('modules', modules), ('theorems', theorems), ('constructions', constructions)]:
            t = replace_array(t, n, ns)
        t = '\n'.join('#print axioms ' + n for n in queries) + '\n\n' + t + '\n' + '\n'.join('#lint in ' + m for m in modules) + '\n'
    output(new + '.lean', imports + t)
reuse = ['SourcePerfectSeparatingCoordinate', 'SourceModularCoordinateNotPower', 'SourceSeparableFixedRootDescent', 'SourceEllipticSpecializationTorsionRange']
paths = [src / (n + '.lean') for n in reuse]
paths += [repo / '.lake/packages/mathlib/Mathlib/FieldTheory/IsAlgClosed/Basic.lean', repo / '.lake/packages/mathlib/Mathlib/FieldTheory/IsAlgClosed/AlgebraicClosure.lean', p / 'marked-algebraic-chart-route-1950.json', p / 'anthropic-diamond-place-charts-1746/S_ModularCurve_exists_injective_doubleCoset_forall_diamondPullbackModL_smul_place_eq_of_ord_pos.lean.txt']
route = dict(recordedUTC=datetime.now(timezone.utc).isoformat(),
 chain='DUB17 Theorem2.6 / DUB18 Cor8.2 -> literal higher symmetric-power continuation -> automorphy -> original all-weight characteristic-zero association -> homogeneous Gamma1 Hecke-character realization -> original genus preservation -> reverse genus -> finite elliptic residue fibers -> original-field marked-point chart and its stabilizers.',
 shorterRoute='The actual finite elliptic-fiber consumer uses ofJ over K(t) and a finite Galois torsion field. Descent to an algebraic extension of the j field suffices for that exact consumer. Original-coordinate separability and native fixed-root descent avoid arbitrary coefficient-curve transport. Normalized-embedding conjugacy proves exhaustion without repeating a torsion/sign-class count. The compiling but incidental variable-change Galois modules 1940-1942 are deferred.',
 assumptionsToDischarge=['Original-coordinate separability derives from its finite degree and simple Laurent pole.', 'Galois covariance fixes every embedding value attached to a rational point.', 'Separable fixed-root descent supplies the embedding in the actual torsion field.', 'Native full-torsion lifting supplies an exact-order point from the actual N-squared count.', 'Normality and generation of the base field by j make all normalized embeddings conjugate and hence prove exhaustion.'],
 remaining='Apply the chart to the actual finite Galois torsion-reduction data, prove finite elliptic place-fiber bounds and reverse genus, then continue original association and higher continuation. Level-one chart special cases remain to be handled if the exact consumer needs them. Acceptance16/20; DUB17--20 OPEN.',
 boundary='Eight focused modules compile; exhaustive audit, promotion and assembled verification pending. The final full-torsion chart derives its Galois/diamond covariance, sign invariance, separation and exhaustion; its explicit normality and full-torsion premises are upstream data supplied by the source finite-field construction.',
 reuseChecked=[dict(path=str(f), sha256=sha(f)) for f in paths])
output('source-marked-algebraic-chart-audit-route-1953.json', json.dumps(route, indent=2) + '\n')
t = (p / 'build_toric_marked_point_canonical_1899.ps1').read_text(encoding='utf-8')
t = re.sub(r'(?m)^\$names=@\(.*$', '$names=@(' + ','.join("'" + m + "'" for m in modules) + ')', t).replace('1899', '1953').replace('toric_marked_point', 'marked_algebraic_chart')
output('build_marked_algebraic_chart_canonical_1953.ps1', t)
replacements = {'SourceToricMarkedPointAudit1': 'SourceMarkedAlgebraicChartAudit1', 'SourceToricMarkedPointDependencyAudit1': 'SourceMarkedAlgebraicChartDependencyAudit1', 'SourceToricMarkedPointScratchOwnership1899': 'SourceMarkedAlgebraicChartScratchOwnership1953', 'record_toric_marked_point_1899': 'record_marked_algebraic_chart_1953'}
t = (p / 'audit_toric_marked_point_1899.ps1').read_text(encoding='utf-8')
for a, b in replacements.items(): t = t.replace(a, b)
output('audit_marked_algebraic_chart_1953.ps1', t)
t = (p / 'record_toric_marked_point_1899.py').read_text(encoding='utf-8')
replacements.update({'source-toric-marked-point-1': 'source-marked-algebraic-chart-1', 'source-toric-marked-point-audit-route-1899': 'source-marked-algebraic-chart-audit-route-1953', 'SOURCE TORIC MARKED POINT': 'SOURCE MARKED ALGEBRAIC CHART', '(15, 66, 73)': str((len(modules), len(queries), len(edges))), '== 15': '== 8', 'linterScopes=15': 'linterScopes=8', 'all 73 required': 'all ' + str(len(edges)) + ' required', 'requiredProofValueEdges=73': 'requiredProofValueEdges=' + str(len(edges)), 'modules=15, queries=66': 'modules=8, queries=8', 'proofEdges=73': 'proofEdges=' + str(len(edges))})
for a, b in replacements.items(): t = t.replace(a, b)
output('record_marked_algebraic_chart_1953.py', t)
print(json.dumps(dict(modules=len(modules), queries=len(queries), proofEdges=len(edges))))
