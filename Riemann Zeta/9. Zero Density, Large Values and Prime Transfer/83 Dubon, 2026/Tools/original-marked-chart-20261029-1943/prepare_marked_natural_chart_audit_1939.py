from pathlib import Path
from datetime import datetime, timezone
import ast, hashlib, json, re

p = Path(__file__).parent
repo = Path(r'E:\Lean\Riemann Zeta')
src = repo / '9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026/Extension/Dubon2026'
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
versions = ['SourceMarkedOrbitMap1935a', 'SourceMarkedNaturalSignChart1936a', 'SourceMarkedSignChartDiamond1937a', 'SourceMarkedOriginalNaturalChart1938b']
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
assert len(queries) == len(set(queries)) == 4
roots = [mc + 'exists_original_natural_marked_chart_generic']
edges = queries + [mc + n for n in ['exists_original_marked_chart_stabilizer_equality', 'exists_point_conjugacy_up_to_sign_of_unit_moves', 'gamma0Unit_surjective', 'signClassGaloisAction', 'signClass_smul_eq_iff', 'signClass_stabilizer_iff', 'normalizedEmbeddingAction', 'normalizedEmbedding_stabilizer_iff', 'normalizedEmbeddingLocalAction']]
edges += [ta + 'signPair_eq_iff']
assert len(edges) == len(set(edges))
cfg = dict(modules=modules, theorems=theorems, constructions=constructions, queries=queries, roots=roots, proofEdges=edges, compileEvidence={m: m + '-1939' for m in modules}, separatelyAxiomChecked=[])
output('source-marked-natural-chart-1-audit-config.json', json.dumps(cfg, indent=2) + '\n')
output('marked-natural-chart-versions-1939.json', json.dumps(files, indent=2) + '\n')
imports = '\n'.join('import ' + m for m in modules) + '\nimport Mathlib.Tactic\n\nopen Lean\n\n'
def replace_array(t, name, names):
    arr = '#[' + ', '.join('`' + n for n in names) + ']'
    t, count = re.subn(r'(?m)^  let ' + name + r' : Array Name := #\[.*$', '  let ' + name + ' : Array Name := ' + arr, t)
    assert count == 1, name
    return t
upstream = []
for fn in ['source-integral-toric-forms-2-audit-config.json', 'source-original-toric-coordinates-3-audit-config.json', 'source-toric-marked-point-1-audit-config.json', 'source-marked-chart-construction-1-audit-config.json', 'source-marked-chart-stabilizer-2-audit-config.json']:
    upstream += json.loads((p / fn).read_text(encoding='utf-8'))['modules']
for old, new in [('SourceToricMarkedPointAudit1', 'SourceMarkedNaturalChartAudit1'), ('SourceToricMarkedPointDependencyAudit1', 'SourceMarkedNaturalChartDependencyAudit1'), ('SourceToricMarkedPointScratchOwnership1899', 'SourceMarkedNaturalChartScratchOwnership1939')]:
    t = (p / (old + '.lean')).read_text(encoding='utf-8')
    t = t[t.index('private def'):]
    t = t.replace('ToricMarkedPoint', 'MarkedNaturalChart').replace('Toric marked point', 'Marked natural chart').replace('SOURCE TORIC MARKED POINT', 'SOURCE MARKED NATURAL CHART')
    if 'Dependency' in old:
        for n, ns in [('roots', roots), ('localModules', modules + upstream), ('required', edges)]:
            t = replace_array(t, n, ns)
        a, b = t.index('  logInfo m!'), t.index('\n\n#eval')
        t = t[:a] + '  logInfo m!"SOURCE MARKED NATURAL CHART DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the VALUE closure of the actual original-field natural chart over the generic j field. Equal stabilizers and signed transitivity construct an injective equivariant map on the actual sign classes. Signed diamond lifts prove exact diamond covariance of the chart, without an unsigned lift. Arbitrary full-torsion field descent, finite elliptic fibers, and reverse genus remain open; DUB17--20 OPEN."' + t[b:]
    elif 'Ownership' in old:
        t = replace_array(t, 'mods', modules)
    else:
        t = t[:t.index('\n#lint')]
        for n, ns in [('modules', modules), ('theorems', theorems), ('constructions', constructions)]:
            t = replace_array(t, n, ns)
        t = '\n'.join('#print axioms ' + n for n in queries) + '\n\n' + t + '\n' + '\n'.join('#lint in ' + m for m in modules) + '\n'
    output(new + '.lean', imports + t)
reuse = ['SL2Reduction', 'SourceCyclicPairOrder', 'SourceEllipticTorsionStructure', 'SourceIntegralGenericIrreducibility', 'SourceEllipticAllLevelCyclicRootBijection', 'SourceEllipticAllLevelCyclicEquivariance', 'SourceEllipticFixedCurvePointMap', 'SourceIntegralDiamondScalarBaseFixed']
paths = [src / (n + '.lean') for n in reuse]
paths += [repo / '.lake/packages/mathlib/Mathlib/FieldTheory/Normal/Basic.lean', repo / '.lake/packages/mathlib/Mathlib/GroupTheory/Index.lean', repo / '.lake/packages/mathlib/Mathlib/GroupTheory/OrderOfElement.lean']
route = dict(recordedUTC=datetime.now(timezone.utc).isoformat(),
 chain='DUB17 Theorem2.6 / DUB18 Cor8.2 -> literal higher symmetric-power continuation -> automorphy -> original all-weight characteristic-zero association -> homogeneous Gamma1 Hecke-character realization -> original genus preservation -> reverse genus -> finite elliptic residue fibers -> original-field marked-point chart and its stabilizers.',
 shorterRoute='Native normal-field extension conjugates normalized original-field embeddings. The already proved diamond coordinate formulas supply every unit generator move up to sign. The native all-level cyclic-quotient bijection, equivariance, and original modular-polynomial irreducibility supply cyclic moves. Combining them proves the required transitive sign orbit without importing or expanding the references full Tate transvection and finite-matrix monodromy developments. Native torsion structure and integral SL2 reduction identify the actual sign-class count with the signed Gamma1 index; native strict antitonicity of subgroup indices then proves equality of the actual point and embedding stabilizers. The stronger unsigned orbit and exact diamond transport remain open, not weakened or silently discharged.',
 assumptionsToDischarge=['The number of actual exact-order elliptic points up to sign is the signed Gamma1 index, with a torsion basis derived from the existing torsion theorem.', 'The original residue diamond action fixes the j coordinate and realizes all residue-unit labels by native integral SL2 lifting.', 'Every normalized original-field embedding is conjugate by a base-field Galois automorphism, using the native normal-extension theorem.', 'The constructed exact-order point is transported by diamond lifts according to the original coordinate action, up to sign.', 'The actual all-level cyclic-quotient correspondence and irreducible modular polynomial produce cyclic-generator conjugacy.', 'The actual constructed point has a Galois orbit containing every exact-order point up to sign, with no orbit or generator-move certificate left in the original-field consumer.', 'The actual original-field embedding stabilizer equals the actual point stabilizer up to sign; both finite-degree and point-count premises are discharged.'],
 remaining='The generic-field chart output is exact. Descent to arbitrary fields with full level-N torsion, finite elliptic fibers, reverse genus, association and higher continuation remain open. The stronger external unsigned transport helper is unnecessary for this exact chart output and is deferred. Acceptance16/20; DUB17--20 OPEN.',
 boundary='Four focused modules compile; exhaustive audit, promotion and assembled verification pending. Exact generic-field Galois and diamond chart covariance, sign invariance and separation are proved.',
 reuseChecked=[dict(path=str(f), sha256=sha(f)) for f in paths])
output('source-marked-natural-chart-audit-route-1939.json', json.dumps(route, indent=2) + '\n')
t = (p / 'build_toric_marked_point_canonical_1899.ps1').read_text(encoding='utf-8')
t = re.sub(r'(?m)^\$names=@\(.*$', '$names=@(' + ','.join("'" + m + "'" for m in modules) + ')', t).replace('1899', '1939').replace('toric_marked_point', 'marked_natural_chart')
output('build_marked_natural_chart_canonical_1939.ps1', t)
replacements = {'SourceToricMarkedPointAudit1': 'SourceMarkedNaturalChartAudit1', 'SourceToricMarkedPointDependencyAudit1': 'SourceMarkedNaturalChartDependencyAudit1', 'SourceToricMarkedPointScratchOwnership1899': 'SourceMarkedNaturalChartScratchOwnership1939', 'record_toric_marked_point_1899': 'record_marked_natural_chart_1939'}
t = (p / 'audit_toric_marked_point_1899.ps1').read_text(encoding='utf-8')
for a, b in replacements.items(): t = t.replace(a, b)
output('audit_marked_natural_chart_1939.ps1', t)
t = (p / 'record_toric_marked_point_1899.py').read_text(encoding='utf-8')
replacements.update({'source-toric-marked-point-1': 'source-marked-natural-chart-1', 'source-toric-marked-point-audit-route-1899': 'source-marked-natural-chart-audit-route-1939', 'SOURCE TORIC MARKED POINT': 'SOURCE MARKED NATURAL CHART', '(15, 66, 73)': str((len(modules), len(queries), len(edges))), '== 15': '== 4', 'linterScopes=15': 'linterScopes=4', 'all 73 required': 'all ' + str(len(edges)) + ' required', 'requiredProofValueEdges=73': 'requiredProofValueEdges=' + str(len(edges)), 'modules=15, queries=66': 'modules=4, queries=4', 'proofEdges=73': 'proofEdges=' + str(len(edges))})
for a, b in replacements.items(): t = t.replace(a, b)
output('record_marked_natural_chart_1939.py', t)
print(json.dumps(dict(modules=len(modules), queries=len(queries), proofEdges=len(edges))))
