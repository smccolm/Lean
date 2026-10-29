from pathlib import Path
from datetime import datetime, timezone
import ast, hashlib, json, re

p = Path(__file__).parent
repo = Path(r'E:\Lean\Riemann Zeta')
src = repo / '9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026/Extension/Dubon2026'
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
versions = ['SourceTateOriginalJCoordinate1900g', 'SourceMarkedChartCoordinateEmbedding1902a', 'SourceMarkedChartVariableInvariants1903b', 'SourceMarkedChartEqualJTransfer1904c', 'SourceMarkedChartInvariantSeparation1905b', 'SourceMarkedChartFieldDescent1906b', 'SourceMarkedChartTorsionDescent1907b', 'SourceMarkedChartEmbeddingBound1908a', 'SourceMarkedChartResidueDegree1909d', 'SourceMarkedChartDescendedPoint1910e', 'SourceMarkedChartOriginalConstruction1911c', 'SourceMarkedChartStabilizerInclusion1912a', 'SourceMarkedChartOriginalStabilizer1913a']
mapping = {v: re.sub(r'\d+[a-z]$', '', v) for v in versions}
modules = list(mapping.values())
base = 'Dubon2026.SourceFunctionField.'
mc, ta = base + 'MarkedChart.', base + 'ToricAnalytic.'
queries, files = [], []

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
    ns = ta if m == 'SourceTateOriginalJCoordinate' else mc
    qs = re.findall(r'(?m)^(?:@\[[^]]*\] )?(theorem|lemma|def|abbrev)\s+(\S+)', t)
    assert all(k in ['theorem', 'lemma'] for k, n in qs)
    queries += [ns + n for k, n in qs]
    c = re.sub(r'(?m)^import (\S+)$', lambda x: 'import ' + mapping.get(x[1], x[1]), t)
    assert re.sub(r'(?m)^import .*\n', '', c) == re.sub(r'(?m)^import .*\n', '', t)
    output(m + '.lean', c)
    files.append(dict(version=v, module=m, sourcePath=str(f), originalSha256=sha(f), canonicalSha256=sha(p / (m + '.lean')), mathematicalBodyIdentical=True))
assert len(queries) == len(set(queries)) == 22
roots = [mc + 'exists_original_marked_chart_stabilizer_inclusion', mc + 'original_normalized_embeddings_finite_and_card_le']
edges = [n for n in queries if n != mc + 'point_eq_or_neg_of_invariant_pair']
edges += [ta + 'exists_originalField_markedToricCoordinates', base + 'IntegralDiamond.residue_original_coordinate_degree_eq_signed_index', base + 'valuation_residue_isAlgClosed', base + 'IntegralSlash.jqModC_eq_discriminant_normalized']
edges += ['Dubon2026.SourceCurve.rationalCoordinateEmbedding', 'Dubon2026.SourceCurve.rationalCoordinateEmbedding_X', 'RatFunc.algEquivOfTranscendental', 'Dubon2026.SourceEllipticVariableChange.variableChangeAddEquiv', 'Dubon2026.SourceEllipticVelu.OddDiscriminant.pointMapHom', 'Dubon2026.SourceEllipticVelu.OddDiscriminant.pointMapHom_injective', 'Dubon2026.SourceEllipticReduction.torsion_mem_specialization_range', 'Dubon2026.SourceEllipticTorsion.actual_torsion_cardinality', 'Dubon2026.SourceEllipticStabilizer.c6_ne_zero_of_j_ne_1728', 'WeierstrassCurve.exists_variableChange_of_j_eq', 'WeierstrassCurve.Affine.Point.X_eq_iff', 'card_algHom_le_finrank', 'IntermediateField.adjoin_algHom_ext', 'IsAlgClosed.lift', 'HasEnoughRootsOfUnity.exists_primitiveRoot']
assert len(edges) == len(set(edges))
cfg = dict(modules=modules, theorems=queries, constructions=[], queries=queries, roots=roots, proofEdges=edges, compileEvidence={m: m + '-1914' for m in modules}, separatelyAxiomChecked=[])
output('source-marked-chart-construction-1-audit-config.json', json.dumps(cfg, indent=2) + '\n')
output('marked-chart-construction-versions-1914.json', json.dumps(files, indent=2) + '\n')
imports = '\n'.join('import ' + m for m in modules) + '\nimport Mathlib.Tactic\n\nopen Lean\n\n'
def replace_array(t, name, names):
    arr = '#[' + ', '.join('`' + n for n in names) + ']'
    t, count = re.subn(r'(?m)^  let ' + name + r' : Array Name := #\[.*$', '  let ' + name + ' : Array Name := ' + arr, t)
    assert count == 1, name
    return t
upstream = []
for fn in ['source-integral-toric-forms-2-audit-config.json', 'source-original-toric-coordinates-3-audit-config.json', 'source-toric-marked-point-1-audit-config.json']:
    upstream += json.loads((p / fn).read_text(encoding='utf-8'))['modules']
for old, new in [('SourceToricMarkedPointAudit1', 'SourceMarkedChartConstructionAudit1'), ('SourceToricMarkedPointDependencyAudit1', 'SourceMarkedChartConstructionDependencyAudit1'), ('SourceToricMarkedPointScratchOwnership1899', 'SourceMarkedChartConstructionScratchOwnership1914')]:
    t = (p / (old + '.lean')).read_text(encoding='utf-8')
    t = t[t.index('private def'):]
    t = t.replace('ToricMarkedPoint', 'MarkedChartConstruction').replace('Toric marked point', 'Marked chart construction').replace('SOURCE TORIC MARKED POINT', 'SOURCE MARKED CHART CONSTRUCTION')
    if 'Dependency' in old:
        for n, ns in [('roots', roots), ('localModules', modules + upstream), ('required', edges)]:
            t = replace_array(t, n, ns)
        a, b = t.index('  logInfo m!'), t.index('\n\n#eval')
        t = t[:a] + '  logInfo m!"SOURCE MARKED CHART CONSTRUCTION DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the VALUE closure of the actual original-field point construction, one stabilizer inclusion, and normalized embedding bound. Native equal-j transfer, torsion descent, coordinate-field embedding, and residue degree discharge the construction premises. The opposite stabilizer inclusion, orbit cardinality, finite elliptic fibers, and reverse genus remain open; DUB17--20 OPEN."' + t[b:]
    elif 'Ownership' in old:
        t = replace_array(t, 'mods', modules)
    else:
        t = t[:t.index('\n#lint')]
        for n, ns in [('modules', modules), ('theorems', queries), ('constructions', [])]:
            t = replace_array(t, n, ns)
        t = '\n'.join('#print axioms ' + n for n in queries) + '\n\n' + t + '\n' + '\n'.join('#lint in ' + m for m in modules) + '\n'
    output(new + '.lean', imports + t)
reuse = ['SourceRationalShiftPowerSpan', 'SourceEllipticVariableAddEquiv', 'SourceEllipticStabilizerInvariantBounds', 'SourceEllipticStandardTorsion', 'SourceResidueClosedValuationField']
paths = [src / (n + '.lean') for n in reuse]
paths += [repo / '.lake/packages/mathlib/Mathlib/LinearAlgebra/FreeModule/Finite/Matrix.lean', repo / '.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean']
route = dict(recordedUTC=datetime.now(timezone.utc).isoformat(),
 chain='DUB17 Theorem2.6 / DUB18 Cor8.2 -> literal higher symmetric-power continuation -> automorphy -> original all-weight characteristic-zero association -> homogeneous Gamma1 Hecke-character realization -> original genus preservation -> reverse genus -> finite elliptic residue fibers -> original-field marked-point chart and its stabilizers.',
 shorterRoute='Use the existing rational-coordinate embedding and native transcendental rational-function equivalence instead of reconstructing fraction fields; use the proved exact Tate point and native equal-j variable change; descend the field embedding by algebraically closed polynomial roots and the point by the existing torsion specialization theorem; bound normalized embeddings by native adjoin extensionality and card_algHom_le_finrank. This avoids a new equalizer/cardinality framework and additional torsion census. The final consumer constructs every chart input from the actual residue field and original Gamma1 field.',
 assumptionsToDischarge=['The literal Tate j invariant equals the original jq series, by an integral discriminant identity before base change, including characteristics two and three.', 'An actual embedding of the original modular-function field and an exact-order point exist over the algebraic closure of the source generic j field, with all unit-multiple coordinate identities.', 'No scalar-compatibility certificate remains in the actual consumer: the common extension is constructed and compatibility is reflexive.', 'The original residue degree proves finiteness and bounds normalized field embeddings by the signed Gamma1 index.', 'Any generic-field automorphism fixing the constructed original-field embedding fixes its actual marked point up to sign; both coordinate invariants separate abscissae in every characteristic.'],
 remaining='The opposite stabilizer inclusion, primitive-point Galois orbit cardinality, diamond lift, finite elliptic-fiber bounds, reverse genus, and downstream association and higher continuation remain required. Acceptance16/20; DUB17--20 OPEN.',
 boundary='Scratch-audited scope only after the checks pass; promotion and assembled verification pending. Only one stabilizer inclusion is claimed.',
 reuseChecked=[dict(path=str(f), sha256=sha(f)) for f in paths])
output('source-marked-chart-construction-audit-route-1914.json', json.dumps(route, indent=2) + '\n')
t = (p / 'build_toric_marked_point_canonical_1899.ps1').read_text(encoding='utf-8')
t = re.sub(r'(?m)^\$names=@\(.*$', '$names=@(' + ','.join("'" + m + "'" for m in modules) + ')', t).replace('1899', '1914').replace('toric_marked_point', 'marked_chart_construction')
output('build_marked_chart_construction_canonical_1914.ps1', t)
replacements = {'SourceToricMarkedPointAudit1': 'SourceMarkedChartConstructionAudit1', 'SourceToricMarkedPointDependencyAudit1': 'SourceMarkedChartConstructionDependencyAudit1', 'SourceToricMarkedPointScratchOwnership1899': 'SourceMarkedChartConstructionScratchOwnership1914', 'record_toric_marked_point_1899': 'record_marked_chart_construction_1914'}
t = (p / 'audit_toric_marked_point_1899.ps1').read_text(encoding='utf-8')
for a, b in replacements.items(): t = t.replace(a, b)
output('audit_marked_chart_construction_1914.ps1', t)
t = (p / 'record_toric_marked_point_1899.py').read_text(encoding='utf-8')
replacements.update({'source-toric-marked-point-1': 'source-marked-chart-construction-1', 'source-toric-marked-point-audit-route-1899': 'source-marked-chart-construction-audit-route-1914', 'SOURCE TORIC MARKED POINT': 'SOURCE MARKED CHART CONSTRUCTION', '(15, 66, 73)': str((len(modules), len(queries), len(edges))), '== 15': '== 13', 'linterScopes=15': 'linterScopes=13', 'all 73 required': 'all ' + str(len(edges)) + ' required', 'requiredProofValueEdges=73': 'requiredProofValueEdges=' + str(len(edges)), 'modules=15, queries=66': 'modules=13, queries=22', 'proofEdges=73': 'proofEdges=' + str(len(edges))})
for a, b in replacements.items(): t = t.replace(a, b)
output('record_marked_chart_construction_1914.py', t)
print(json.dumps(dict(modules=len(modules), queries=len(queries), proofEdges=len(edges))))
