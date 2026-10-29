from pathlib import Path
from datetime import datetime, timezone
import ast, hashlib, json, re

p = Path(__file__).parent
r = Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
versions = json.loads((p / 'gamma-one-kummer-versions-1348.json').read_text(encoding='utf-8'))
prior = json.loads((p / 'source-gamma-one-specialization-1-audit-config.json').read_text(encoding='utf-8'))
mods = list(versions)
ths, defs = [], []
for m in mods:
    code = re.sub(r'--[^\n]*', '', re.sub(r'/\-.*?\-/', '', (p / (m + '.lean')).read_text(encoding='utf-8'), flags=re.S))
    ns = re.search(r'^namespace (\S+)', code, re.M)[1] + '.'
    ths += [ns + x for x in re.findall(r'^theorem\s+([\w.\x27]+)', code, re.M)]
    defs += [ns + x for x in re.findall(r'^@\[reducible\] local instance\s+([\w.\x27]+)', code, re.M)]
cn = 'Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction.'
cv = 'Dubon2026.SourceCurve.'
rp = cv + 'RegularProlongation.'
roots = [cn + 'exists_gammaOne_picard_torsion_injective_of_degree_genus_eq']
edges = ths + defs + prior['queries'] + [
    cv + 'canonical_degree_map_of_unramified',
    cv + 'finite_coordinate_canonical_degree_eq_genusFF',
    rp + 'exists_kummer_regular_prolongations',
    rp + 'JointChartConstants.exists_full_lifted_residue_polynomial_basis',
    rp + 'JointChartConstants.exists_integral_coords_of_full_chart_basis',
    rp + 'JointChartConstants.exists_good_coordinate_denominator',
    rp + 'JointChartConstants.finite_overlap_of_good_basis',
    rp + 'JointChartConstants.common_constants_of_finite_overlap',
    rp + 'JointChartAssembly.eventual_uniform_residue_chart_dimension',
    rp + 'Joint.finrank_joint_residue_span',
    rp + 'Joint.span_residue_pole_space_le_chart_intersection',
    cv + 'exists_pole_space_generating_window_of_separating_coordinate',
    cv + 'genusFF_eq_zero_index',
    cv + 'degree_poleDivisor_eq_finrank_separating',
    cv + 'ConstantReduction.pic0_eq_zero_of_power_lifting',
    cv + 'algebraicClosure_rat_valuation_krullDimLE_one',
]
assert (len(mods), len(ths), len(defs), len(edges)) == (11, 13, 1, 44)
assert len(set(edges)) == len(edges)
cfg = dict(modules=mods, theorems=ths, constructions=defs, queries=ths + defs,
           roots=roots, proofEdges=edges, localModules=prior['modules'] + mods,
           separatelyAxiomChecked=[], compileEvidence={m: m + '-1348' for m in mods})

def write(name, text):
    f = p / name
    assert not f.exists(), f
    f.write_text(text, encoding='utf-8')

stem = 'source-gamma-one-kummer-1'
write(stem + '-audit-config.json', json.dumps(cfg, indent=2) + '\n')
arr = lambda xs: '#[' + ', '.join(chr(96) + x for x in xs) + ']'
old, new = 'SourceGammaOneSpecialization', 'SourceGammaOneKummer'
for a, b in [('Audit1', 'Audit1'), ('DependencyAudit1', 'DependencyAudit1'),
             ('ScratchOwnership1334', 'ScratchOwnership1349')]:
    s = (p / (old + a + '.lean')).read_text(encoding='utf-8')
    s = '\n'.join('import ' + m for m in mods) + '\nimport Mathlib.Tactic\n' + s[s.index('\nopen Lean'):]
    if a == 'Audit1':
        s = re.sub(r'(#print axioms [^\n]+\n)+', ''.join('#print axioms ' + x + '\n' for x in cfg['queries']), s, count=1)
        for k, v in [('modules', mods), ('theorems', ths), ('constructions', defs)]:
            s = re.sub(r'let ' + k + r' : Array Name := #\[[^\n]*\]', 'let ' + k + ' : Array Name := ' + arr(v), s)
        s = re.sub(r'#lint in [^\n]+\n', '', s).rstrip() + '\n\n' + ''.join('#lint in ' + m + '\n' for m in mods)
    elif a == 'DependencyAudit1':
        for k, v in [('roots', roots), ('localModules', cfg['localModules']), ('required', edges)]:
            s = re.sub(r'let ' + k + r' : Array Name := #\[[^\n]*\]', 'let ' + k + ' : Array Name := ' + arr(v), s)
        start = s.index(' occur in the ')
        end = s.index('; DUB17--20 OPEN.', start)
        s = s[:start] + (' occur in the proof value closure of the actual original Gamma1 constant reduction '
             'with an injective prime-to-residue Picard torsion map, constructed from coordinate-degree '
             'and actual genus equality. The original Kummer degree and unramified genus identity, '
             'finite overlap, common constants, joint pole-space comparison, residue genus inequality, '
             'power lifting and prime/all-order torsion kernel arguments are derived. Degree and genus '
             'preservation, diamond integrality and original Tate Frobenius/inertia remain unresolved') + s[end:]
    else:
        s = re.sub(r'let mods : Array Name := #\[[^\n]*\]', 'let mods : Array Name := ' + arr(mods), s)
    s = s.replace('GAMMA ONE SPECIALIZATION', 'GAMMA ONE KUMMER')
    write(new + b + '.lean', s)

sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
reuse = [r / 'Extension/Dubon2026' / (m + '.lean') for m in [
    'SourceCurveKummerUnramified', 'SourceCurveFiniteCoordinateCanonicalDegree',
    'SourceCurveUnramifiedCanonicalDegree', 'SourceKummerRegularProlongationsR2',
    'SourceJointChartFullBasis', 'SourceJointChartIntegralCoordinates',
    'SourceJointChartGoodDenominators', 'SourceJointChartFiniteOverlap',
    'SourceJointChartConstantsOfFiniteOverlap', 'SourceJointChartUniformResidues',
    'SourceJointReductionDimension', 'SourceJointReductionPoleCharts',
    'SourceSeparableCoordinateChartGeneration', 'SourceModularKummerPowerLifting',
    'SourceModularJointGenusInequality', 'SourceModularGenusTorsionInjectivity',
    'SourceCurveReductionPrimeKernel', 'SourceGammaOneResidueSeparability']]
reuse += [r / 'Tools/curve-reuse-20261028-1283/review-manifest.json',
          p / 'gamma-one-route-review-1326.md']
route = dict(recordedUTC=datetime.now(timezone.utc).isoformat(),
    chain='DUB17 Theorem 2.6 / DUB18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> original Gamma1 Picard/H1/Tate realization -> Frobenius/inertia -> prime-to-residue Picard specialization injectivity.',
    reuseChecked=[dict(path=str(f), sha256=sha(f)) for f in reuse],
    shorterRoute='Reuse native Kummer valuation, unramified canonical-degree, full joint basis, integral-coordinate, denominator, finite-overlap, common-constants and pole-dimension proofs directly. Their generic separating-coordinate composition bypasses the Gamma0-specific wrapper chain. The original Gamma1 consumer derives its reductions and total coordinate degree; the native strong-induction argument handles all invertible torsion orders. The superseded Gamma1 chart wrappers remain inert snapshots and are not promoted.',
    assumptionsToDischarge=[
        'The actual original Gamma1 Kummer cover has degree q, is unramified, and satisfies g(E)-1=q*(g(F)-1).',
        'Separating reduced j and total degree derive finite overlap, common constants, joint residue/pole dimensions and q*g(residue)<=g(E).',
        'Actual coordinate-degree and genus equality force prime-root lifting and trivial prime-order and all invertible-order Picard kernels.',
        'The constructed original constant reduction, with exactly the original coefficient regular prolongation, has an injective map on every invertible Picard torsion subgroup.'],
    remaining='Actual original Gamma1 coordinate-degree equality and genus preservation remain explicit geometric inputs; they and diamond integrality are not proved here. Original Tate Frobenius/inertia, arithmetic realization, all-weight association, automorphy and full higher continuation remain. 16/20; DUB17--20 OPEN.',
    externalBuild=False, externalImport=False, rootPinsChanged=False, proofLimitsChanged=False)
routefile = 'source-gamma-one-kummer-audit-route-1349.json'
write(routefile, json.dumps(route, indent=2) + '\n')
s = (p / 'record_gamma_one_specialization_1334.py').read_text(encoding='utf-8')
for a, b in [('source-gamma-one-specialization-audit-route-1334', routefile[:-5]),
             ('source-gamma-one-specialization-1', stem), (old, new),
             ('ScratchOwnership1334', 'ScratchOwnership1349'),
             ('GAMMA ONE SPECIALIZATION', 'GAMMA ONE KUMMER')]:
    s = s.replace(a, b)
s = s.replace('(6, 14, 28)', '(11, 14, 44)').replace('== 6', '== 11')
s = s.replace('linterScopes=6', 'linterScopes=11').replace('modules=6', 'modules=11')
s = s.replace('all 28 required', 'all 44 required').replace('requiredProofValueEdges=28', 'requiredProofValueEdges=44').replace('proofEdges=28', 'proofEdges=44')
ast.parse(s)
write('record_gamma_one_kummer_1349.py', s)
s = (p / 'audit_gamma_one_specialization_1334.ps1').read_text(encoding='utf-8-sig')
for a, b in [(old, new), ('ScratchOwnership1334', 'ScratchOwnership1349'),
             ('record_gamma_one_specialization_1334', 'record_gamma_one_kummer_1349')]:
    s = s.replace(a, b)
write('audit_gamma_one_kummer_1349.ps1', s)
print(json.dumps(dict(modules=len(mods), queries=len(ths + defs), proofEdges=len(edges))))
