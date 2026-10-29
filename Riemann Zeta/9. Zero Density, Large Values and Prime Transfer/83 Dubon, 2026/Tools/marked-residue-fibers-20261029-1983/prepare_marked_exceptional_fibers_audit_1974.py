from pathlib import Path
from datetime import datetime, timezone
import ast, hashlib, json, re

p = Path(__file__).parent
repo = Path(r'E:\Lean\Riemann Zeta')
src = repo / '9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026/Extension/Dubon2026'
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
versions = ['SourceMarkedSignPermutation1961c', 'SourceMarkedSignFreeOrbits1962c', 'SourceMarkedSignFiberFactor1964c', 'SourceMarkedPeriodicFiberBound1965a', 'SourceMarkedTorsionReductionEquiv1966b', 'SourceMarkedQuadraticFiberBounds1967c', 'SourceMarkedReducedFiberChart1968c', 'SourceMarkedOriginalResidueFiberFive1969e', 'SourceMarkedOriginalTameFiberBounds1970b', 'SourceMarkedFullInertiaLifts1973a', 'SourceMarkedOriginalResidueFiberTwo1971c', 'SourceMarkedOriginalResidueFiberThree1972c']
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
    ns = re.search(r'(?m)^namespace (\S+)', t)[1] + '.'
    qs = re.findall(r'(?m)^(?:@\[[^]]*\] )?(theorem|lemma|def|abbrev)\s+(\S+)', t)
    queries += [ns + n for k, n in qs]
    theorems += [ns + n for k, n in qs if k in ['theorem', 'lemma']]
    constructions += [ns + n for k, n in qs if k in ['def', 'abbrev']]
    c = re.sub(r'(?m)^import (\S+)$', lambda x: 'import ' + mapping.get(x[1], x[1]), t)
    assert re.sub(r'(?m)^import .*\n', '', c) == re.sub(r'(?m)^import .*\n', '', t)
    output(m + '.lean', c)
    files.append(dict(version=v, module=m, sourcePath=str(f), originalSha256=sha(f), canonicalSha256=sha(p / (m + '.lean')), mathematicalBodyIdentical=True))
assert len(queries) == len(set(queries)) == 20
roots = [mc + n for n in ['original_two_mul_card_j_1728_fiber_le_of_five_le', 'original_three_mul_card_j_zero_fiber_le_of_five_le', 'exists_original_residue_marked_fiber_of_char_two', 'exists_original_residue_marked_fiber_of_char_three']]
separate = [ta + 'signClassesEquiv_pair']
edges = [n for n in queries if n not in separate]
edges += [mc + 'exists_original_marked_fiber_chart', ta + 'actual_point_signClasses_card', 'Dubon2026.SourceEllipticReduction.torsion_mem_specialization_range', 'Dubon2026.SourceEllipticDivisionField.exists_prescribed_ofJ_full_inertia_image', 'Dubon2026.SourceEllipticDivisionField.exists_char_two_exceptional_full_inertia_image', 'Dubon2026.SourceEllipticDivisionField.exists_char_three_exceptional_full_inertia_image', 'Dubon2026.SourceManin.two_mul_natCard_orb', 'Dubon2026.SourceManin.three_mul_natCard_orb', 'Dubon2026.SourceEllipticExceptional.quartic_action_square', 'Dubon2026.SourceEllipticExceptional.cubic_action_relation', 'Dubon2026.SourceEllipticExceptional.orbQ_eq_iff_pow_lt']

assert len(edges) == len(set(edges))
cfg = dict(modules=modules, theorems=theorems, constructions=constructions, queries=queries, roots=roots, proofEdges=edges, compileEvidence={m: m + '-1974' for m in modules}, separatelyAxiomChecked=separate)
output('source-marked-exceptional-fibers-1-audit-config.json', json.dumps(cfg, indent=2) + '\n')
output('marked-exceptional-fibers-versions-1974.json', json.dumps(files, indent=2) + '\n')
imports = '\n'.join('import ' + m for m in modules) + '\nimport Mathlib.Tactic\n\nopen Lean\n\n'
def replace_array(t, name, names):
    arr = '#[' + ', '.join('`' + n for n in names) + ']'
    t, count = re.subn(r'(?m)^  let ' + name + r' : Array Name := #\[.*$', '  let ' + name + ' : Array Name := ' + arr, t)
    assert count == 1, name
    return t
upstream = []
seen = set(modules)
def local_imports(m):
    for n in re.findall(r'(?m)^import (\S+)$', (p / (m + '.lean')).read_text(encoding='utf-8')):
        if '.' not in n and n not in seen and (p / (n + '.lean')).exists():
            seen.add(n); upstream.append(n); local_imports(n)
for m in modules: local_imports(m)

for old, new in [('SourceToricMarkedPointAudit1', 'SourceMarkedExceptionalFibersAudit1'), ('SourceToricMarkedPointDependencyAudit1', 'SourceMarkedExceptionalFibersDependencyAudit1'), ('SourceToricMarkedPointScratchOwnership1899', 'SourceMarkedExceptionalFibersScratchOwnership1974')]:
    t = (p / (old + '.lean')).read_text(encoding='utf-8')
    t = t[t.index('private def'):]
    t = t.replace('ToricMarkedPoint', 'MarkedExceptionalFibers').replace('Toric marked point', 'Marked algebraic chart').replace('SOURCE TORIC MARKED POINT', 'SOURCE MARKED EXCEPTIONAL FIBERS')
    if 'Dependency' in old:
        for n, ns in [('roots', roots), ('localModules', modules + upstream), ('required', edges)]:
            t = replace_array(t, n, ns)
        a, b = t.index('  logInfo m!'), t.index('\n\n#eval')
        t = t[:a] + '  logInfo m!"SOURCE MARKED EXCEPTIONAL FIBERS DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the VALUE closure of the two actual original Gamma1 tame elliptic-fiber bounds and the two wild residue-point charts. Native full inertia specialization discharges finite fields, full torsion, positive-order places and automorphism lifts. Actual torsion reduction gives exact-order bijection. For N greater than three, native quadratic automorphism identities give free sign-class actions and exact factors two and three without an adapted torsion basis. Small levels, wild differential contributions and reverse genus remain open; DUB17--20 OPEN."' + t[b:]

    elif 'Ownership' in old:
        t = replace_array(t, 'mods', modules)
    else:
        t = t[:t.index('\n#lint')]
        for n, ns in [('modules', modules), ('theorems', theorems), ('constructions', constructions)]:
            t = replace_array(t, n, ns)
        t = '\n'.join('#print axioms ' + n for n in queries) + '\n\n' + t + '\n' + '\n'.join('#lint in ' + m for m in modules) + '\n'
    output(new + '.lean', imports + t)
reuse = ['SourceEllipticSpecializationTorsionRange', 'SourceEllipticPrescribedFullInertiaImage', 'SourceEllipticCharTwoFullInertiaImage', 'SourceEllipticCharThreeFullInertiaImage', 'SourceMarkedTorsionActualCount', 'SourceManinOrbitCount', 'SourceCyclicOrbitClassification', 'SourceEllipticQuarticModel', 'SourceEllipticCubicAction', 'SourceModularCharTwoDifferentialSum', 'SourceModularCharThreeDifferentialSum']
paths = [src / (n + '.lean') for n in reuse]
route = dict(recordedUTC=datetime.now(timezone.utc).isoformat(),
 chain='DUB17 Theorem2.6 / DUB18 Cor8.2 -> literal higher symmetric-power continuation -> automorphy -> original all-weight characteristic-zero association -> homogeneous Gamma1 Hecke-character realization -> original genus preservation -> reverse genus -> actual original Gamma1 elliptic residue fibers.',
 shorterRoute='For N greater than three, actual quartic and cubic point identities exclude fixed primitive sign classes. Native orbit counts therefore give factors two and three without adapted torsion bases or unsigned generator transport. Native full-inertia specialization in every characteristic supplies the finite field, full torsion, positive-order place and lifts; native torsion reduction transports the original chart to actual residue points. The two tame numerical bounds are exact original-field consumers. Wild charts are assembled but their stronger differential bounds remain required.',
 assumptionsToDischarge=['Native specialization constructs all finite Galois, full torsion and positive-order inputs of the original chart.', 'The actual N-squared torsion count and native torsion theorem make reduction bijective on exact-order points.', 'Full inertia image up to sign yields invariance under actual residue-curve automorphisms.', 'For N greater than three, quartic and cubic identities exclude fixed sign classes.', 'Native finite orbit counts and the actual signed Gamma1 index count derive the two tame numerical bounds.'],
 remaining='Handle small levels without losing the all-level contract, derive the wild differential contributions, and assemble reverse genus; then continue original association and higher continuation. Acceptance16/20; DUB17--20 OPEN.',
 boundary='Twelve focused modules compile; exhaustive audit, promotion and assembled verification pending. Tame bounds assume precisely N greater than three and residue characteristic at least five. Wild chart endpoints cover characteristics two and three with N at least two away from characteristic. The elementary sign-pair evaluation lemma is separately axiom-checked and is not claimed as a consumed endpoint dependency.',
 separatelyAxiomChecked=separate,
 reuseChecked=[dict(path=str(f), sha256=sha(f)) for f in paths])
output('source-marked-exceptional-fibers-audit-route-1974.json', json.dumps(route, indent=2) + '\n')

t = (p / 'build_toric_marked_point_canonical_1899.ps1').read_text(encoding='utf-8')
t = re.sub(r'(?m)^\$names=@\(.*$', '$names=@(' + ','.join("'" + m + "'" for m in modules) + ')', t).replace('1899', '1974').replace('toric_marked_point', 'marked_exceptional_fibers')
output('build_marked_exceptional_fibers_canonical_1974.ps1', t)
replacements = {'SourceToricMarkedPointAudit1': 'SourceMarkedExceptionalFibersAudit1', 'SourceToricMarkedPointDependencyAudit1': 'SourceMarkedExceptionalFibersDependencyAudit1', 'SourceToricMarkedPointScratchOwnership1899': 'SourceMarkedExceptionalFibersScratchOwnership1974', 'record_toric_marked_point_1899': 'record_marked_exceptional_fibers_1974'}
t = (p / 'audit_toric_marked_point_1899.ps1').read_text(encoding='utf-8')
for a, b in replacements.items(): t = t.replace(a, b)
output('audit_marked_exceptional_fibers_1974.ps1', t)
t = (p / 'record_toric_marked_point_1899.py').read_text(encoding='utf-8')
replacements.update({'source-toric-marked-point-1': 'source-marked-exceptional-fibers-1', 'source-toric-marked-point-audit-route-1899': 'source-marked-exceptional-fibers-audit-route-1974', 'SOURCE TORIC MARKED POINT': 'SOURCE MARKED EXCEPTIONAL FIBERS', '(15, 66, 73)': str((len(modules), len(queries), len(edges))), '== 15': '== 12', 'linterScopes=15': 'linterScopes=12', 'all 73 required': 'all ' + str(len(edges)) + ' required', 'requiredProofValueEdges=73': 'requiredProofValueEdges=' + str(len(edges)), 'modules=15, queries=66': 'modules=12, queries=20', 'proofEdges=73': 'proofEdges=' + str(len(edges))})
for a, b in replacements.items(): t = t.replace(a, b)
output('record_marked_exceptional_fibers_1974.py', t)
print(json.dumps(dict(modules=len(modules), queries=len(queries), proofEdges=len(edges))))
