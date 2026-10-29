from pathlib import Path
from datetime import datetime, timezone
import ast, hashlib, json, re

p = Path(__file__).parent
r = Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
versions = json.loads((p / 'gamma-one-specialization-versions-1333.json').read_text(encoding='utf-8'))
mods = list(versions)
ths, defs = [], []
for m in mods:
    code = re.sub(r'--[^\n]*', '', re.sub(r'/\-.*?\-/', '', (p / (m + '.lean')).read_text(encoding='utf-8'), flags=re.S))
    ns = re.search(r'^namespace (\S+)', code, re.M)[1] + '.'
    ths += [ns + x for x in re.findall(r'^theorem\s+([\w.\x27]+)', code, re.M)]
    defs += [ns + x for x in re.findall(r'^@\[reducible\] local instance\s+([\w.\x27]+)', code, re.M)]
cn = 'Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction.'
roots = [cn + 'exists_gammaOne_constant_reduction_of_degree_genus_eq']
edges = ths + defs + [
    cn + 'regularProlongation',
    cn + 'finite_residueCoordinate_and_degree_le',
    cn + 'isSeparable_residueCoordinate',
    cn + 'regularProlongation_jCoordinateOver',
    'Dubon2026.SourceFunctionField.valuation_residue_isAlgClosed',
    'Dubon2026.SourceFunctionField.GammaOne.functionFieldOver_isCurveOver',
    'Dubon2026.SourceCurve.hasPrincipalDivisors_closed_of_separating_coordinate',
    'Dubon2026.SourceCurve.place_residue_bijective_of_finite_coordinate',
    'Dubon2026.SourceCurve.degree_poleDivisor_eq_finrank_separating',
    'Dubon2026.SourceCurve.genusFF_eq_zero_index',
    'Dubon2026.SourceCurve.RegularProlongation.finrank_span_residue_eq_finrank\x27',
    'Dubon2026.SourceCurve.RegularProlongation.residue_mem_pole_space',
    'Dubon2026.SourceCurve.RegularProlongation.exists_principal_divisor_reduction_map',
    'Dubon2026.SourceCurve.ConstantReduction.ofPlaceMap',
]
assert (len(mods), len(ths), len(defs), len(edges)) == (6, 13, 1, 28)
cfg = dict(modules=mods, theorems=ths, constructions=defs, queries=ths + defs,
           roots=roots, proofEdges=edges, localModules=mods, separatelyAxiomChecked=[],
           compileEvidence={m: m + '-1333' for m in mods})

def write(name, text):
    f = p / name
    assert not f.exists(), f
    f.write_text(text, encoding='utf-8')

stem = 'source-gamma-one-specialization-1'
write(stem + '-audit-config.json', json.dumps(cfg, indent=2) + '\n')
arr = lambda xs: '#[' + ', '.join(chr(96) + x for x in xs) + ']'
old, new = 'SourceGammaOneHeckeDegree', 'SourceGammaOneSpecialization'
for a, b in [('Audit1', 'Audit1'), ('DependencyAudit1', 'DependencyAudit1'),
             ('ScratchOwnership1297', 'ScratchOwnership1334')]:
    s = (p / (old + a + '.lean')).read_text(encoding='utf-8')
    s = '\n'.join('import ' + m for m in mods) + '\nimport Mathlib.Tactic\n' + s[s.index('\nopen Lean'):]
    if a == 'Audit1':
        s = re.sub(r'(#print axioms [^\n]+\n)+', ''.join('#print axioms ' + x + '\n' for x in cfg['queries']), s, count=1)
        for k, v in [('modules', mods), ('theorems', ths), ('constructions', defs)]:
            s = re.sub(r'let ' + k + r' : Array Name := #\[[^\n]*\]', 'let ' + k + ' : Array Name := ' + arr(v), s)
        s = re.sub(r'#lint in [^\n]+\n', '', s).rstrip() + '\n\n' + ''.join('#lint in ' + m + '\n' for m in mods)
    elif a == 'DependencyAudit1':
        for k, v in [('roots', roots), ('localModules', mods), ('required', edges)]:
            s = re.sub(r'let ' + k + r' : Array Name := #\[[^\n]*\]', 'let ' + k + ' : Array Name := ' + arr(v), s)
        start = s.index(' occur in the ')
        end = s.index('; DUB17--20 OPEN.', start)
        s = s[:start] + (' occur in the proof value closure of the original Gamma1 constant reduction '
             'constructed from coordinate-degree and actual genus equality. Actual residue curve geometry, '
             'pole-space dimensions, both integral chart lifts and principal-divisor compatibility are derived. '
             'Degree and genus equality, diamond integrality, prime-to-residue Picard torsion injectivity '
             'and original Tate Frobenius/inertia remain unresolved') + s[end:]
    else:
        s = re.sub(r'let mods : Array Name := #\[[^\n]*\]', 'let mods : Array Name := ' + arr(mods), s)
    s = s.replace('GAMMA ONE HECKE DEGREE', 'GAMMA ONE SPECIALIZATION')
    write(new + b + '.lean', s)

sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
reuse = [r / 'Extension/Dubon2026' / (m + '.lean') for m in [
    'SourceGammaOneResidueSeparability', 'SourceCurveFiniteCoordinateGenusMaximum',
    'SourceModularGenusPoleLifting', 'SourceModularIntegralChartLifting',
    'SourceReductionPrincipalDivisorMap', 'SourceModularGenusConstantReductionR2',
    'SourceCurveReductionPicardR2', 'SourceCurveFiniteCoordinateResidues']]
route = dict(recordedUTC=datetime.now(timezone.utc).isoformat(),
    chain='DUB17 Theorem 2.6 / DUB18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> original Gamma1 Picard/H1/Tate realization -> Frobenius/inertia -> original coefficient specialization.',
    reuseChecked=[dict(path=str(f), sha256=sha(f)) for f in reuse],
    shorterRoute='Reuse native separating-coordinate principal divisors, finite place residues, pole/genus dimension maxima, regular-prolongation residue dimensions and global two-chart gluing. The inverse chart is obtained by applying the same coordinate-lifting theorem to the inverse unit, using equality of the rational coordinate fields. No new curve, divisor, Riemann--Roch or Picard interface is introduced.',
    assumptionsToDischarge=['Actual original Gamma1 residue curve geometry is derived from its proved finite separating j.',
        'Coordinate-degree equality and actual adelic-genus equality now imply both integral chart lifts and a degree-preserving place map compatible with every principal divisor.',
        'The literal Gamma1 consumer discharges finite index and translation membership and returns a constant reduction whose regular prolongation is exactly the original coefficient reduction.'],
    remaining='Coordinate-degree equality and actual genus equality remain explicit geometric inputs. They, diamond integrality and prime-to-residue Picard torsion injectivity still require proofs. Original Tate Frobenius/inertia, arithmetic realization, all-weight association, automorphy and full higher continuation remain. 16/20; DUB17--20 OPEN.',
    priorRouteReview=dict(path=str(p / 'gamma-one-route-review-1326.md'), sha256=sha(p / 'gamma-one-route-review-1326.md')),
    externalBuild=False, externalImport=False, rootPinsChanged=False, proofLimitsChanged=False)
routefile = 'source-gamma-one-specialization-audit-route-1334.json'
write(routefile, json.dumps(route, indent=2) + '\n')
s = (p / 'record_gamma_one_hecke_degree_1297.py').read_text(encoding='utf-8')
for a, b in [('source-gamma-one-hecke-degree-audit-route-1297', routefile[:-5]),
             ('source-gamma-one-hecke-degree-1', stem), (old, new),
             ('ScratchOwnership1297', 'ScratchOwnership1334'),
             ('GAMMA ONE HECKE DEGREE', 'GAMMA ONE SPECIALIZATION')]:
    s = s.replace(a, b)
s = s.replace('(4, 14, 22)', '(6, 14, 28)').replace('== 4', '== 6')
s = s.replace('linterScopes=4', 'linterScopes=6').replace('modules=4', 'modules=6')
s = s.replace('all 22 required', 'all 28 required').replace('requiredProofValueEdges=22', 'requiredProofValueEdges=28').replace('proofEdges=22', 'proofEdges=28')
ast.parse(s)
write('record_gamma_one_specialization_1334.py', s)
s = (p / 'audit_gamma_one_hecke_degree_1297.ps1').read_text(encoding='utf-8')
for a, b in [(old, new), ('ScratchOwnership1297', 'ScratchOwnership1334'),
             ('record_gamma_one_hecke_degree_1297', 'record_gamma_one_specialization_1334')]:
    s = s.replace(a, b)
write('audit_gamma_one_specialization_1334.ps1', s)
print(json.dumps(dict(modules=len(mods), queries=len(ths + defs), proofEdges=len(edges))))
