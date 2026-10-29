from pathlib import Path
from datetime import datetime, timezone
import ast, hashlib, json, re

p = Path(__file__).parent
r = Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
versions = json.loads((p / 'gamma-one-gauss-norm-versions-1356.json').read_text(encoding='utf-8'))
prior = json.loads((p / 'source-gamma-one-specialization-1-audit-config.json').read_text(encoding='utf-8'))
mods = list(versions)
ths, defs = [], []
for m in mods:
    code = re.sub(r'--[^\n]*', '', re.sub(r'/\-.*?\-/', '', (p / (m + '.lean')).read_text(encoding='utf-8'), flags=re.S))
    ns = re.search(r'^namespace (\S+)', code, re.M)[1] + '.'
    ths += [ns + x for x in re.findall(r'^theorem\s+([\w.\x27]+)', code, re.M)]
    defs += [ns + x for x in re.findall(r'^def\s+([\w.\x27]+)', code, re.M)]
sf = 'Dubon2026.SourceFunctionField.'
gn = sf + 'GammaOne.'
cn = gn + 'CoefficientReduction.'
roots = [cn + 'exists_gammaOne_hecke_gauss_norm_reduction_of_degree_eq']
edges = ths + defs + [
    cn + 'regularProlongation',
    'Dubon2026.SourceCurve.RegularProlongation.isIntegral_coordinate_intersection',
    gn + 'ConstantField.arithmeticDiamondHom_j',
    gn + 'ConstantField.arithmeticDiamondAut',
    cn + 'heckeBeta_mem_gaussRing',
    cn + 'heckeBetaGauss',
    cn + 'heckeBetaGauss_resHom',
    gn + 'exists_gammaOne_hecke_norm_beta_product',
    gn + 'HeckeNorm.diamondLaurentProduct_residue',
    cn + 'resHom_eq',
    cn + 'wit_spec',
    sf + 'primeRootValuationUnit_coe',
    sf + 'qExpand_injective',
    cn + 'finite_residueCoordinate_and_degree_le',
    cn + 'transcendental_residueJCoordinate',
    cn + 'regularProlongation_jCoordinateOver',
    cn + 'specializationResidueAlgebra',
]
assert (len(mods), len(ths), len(defs), len(edges)) == (6, 7, 1, 25)
assert len(set(edges)) == len(edges)
cfg = dict(modules=mods, theorems=ths, constructions=defs, queries=ths + defs,
           roots=roots, proofEdges=edges, localModules=prior['modules'] + mods,
           separatelyAxiomChecked=[], compileEvidence={m: m + '-1356' for m in mods})

def write(name, text):
    f = p / name
    assert not f.exists(), f
    f.write_text(text, encoding='utf-8')

stem = 'source-gamma-one-gauss-norm-1'
write(stem + '-audit-config.json', json.dumps(cfg, indent=2) + '\n')
arr = lambda xs: '#[' + ', '.join(chr(96) + x for x in xs) + ']'
old, new = 'SourceGammaOneSpecialization', 'SourceGammaOneGaussNorm'
for a, b in [('Audit1', 'Audit1'), ('DependencyAudit1', 'DependencyAudit1'),
             ('ScratchOwnership1334', 'ScratchOwnership1357')]:
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
        s = s[:start] + (' occur in the proof value closure of actual original Gamma1 Hecke norm '
             'Gauss integrality and its exact diamond/coefficient-Frobenius/q-Frobenius residue formula. '
             'Coordinate-degree preservation derives diamond Gauss preservation; native integral '
             'fraction witnesses and primitive normalization derive the full norm reduction. No '
             'coefficientwise-integral diamond representative is required. Actual degree and genus '
             'preservation and original Tate Frobenius/inertia remain unresolved') + s[end:]
    else:
        s = re.sub(r'let mods : Array Name := #\[[^\n]*\]', 'let mods : Array Name := ' + arr(mods), s)
    s = s.replace('GAMMA ONE SPECIALIZATION', 'GAMMA ONE GAUSS NORM')
    write(new + b + '.lean', s)

sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
reuse = [r / 'Extension/Dubon2026' / (m + '.lean') for m in [
    'SourceReductionIntegralCoordinates', 'SourceReductionFiniteIntegrality',
    'SourceReductionRegularComparison', 'SourceGammaOneArithmeticDiamond',
    'SourceGammaOneGaussValuation', 'SourceGammaOneGaussResidueHom',
    'SourceGammaOneGaussConstants', 'SourceGammaOneRegularProlongation',
    'SourceGammaOneHeckeGauss', 'SourceGammaOneHeckeMixedLaurentReduction',
    'SourceGammaOneHeckeDiamondNorm', 'SourceGammaOneHeckeIntegralDiamondReduction',
    'SourceFrickeLaurentGeneratorIntegrality', 'SourceBoundedFrickeLaurentField']]
reuse += [p / 'gamma-one-route-review-1326.md',
    p / 'source-gamma-one-kummer-1-scratch-receipt.json']
route = dict(recordedUTC=datetime.now(timezone.utc).isoformat(),
    chain='DUB17 Theorem 2.6 / DUB18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> original Gamma1 Picard/H1/Tate realization -> geometric Frobenius/inertia -> actual Hecke norm and residue compatibility.',
    reuseChecked=[dict(path=str(f), sha256=sha(f)) for f in reuse],
    shorterRoute='The existing finite-coordinate theorem already proves prolongation integers integral over the intersection with the rational j-field under degree preservation. The exact arithmetic diamond fixes j and constants, so integral closedness preserves the Gauss ring. This removes the need for a separate valuation-uniqueness or integral-model argument for diamond preservation. The Gauss ring uses integral fractions, which need not have coefficientwise-integral Laurent expansions. Apply the existing two-input norm product separately to the numerator and denominator, prove the reduced denominator nonzero, and reflect beta integrality via the existing primitive constant normalization. This proves the required norm reduction on all actual Gauss integers, instead of trying to manufacture the unnecessary stronger Laurent representative.',
    assumptionsToDischarge=[
        'Actual coordinate-degree preservation implies preservation of the original coefficient Gauss ring by every arithmetic diamond.',
        'The original beta Hecke map reflects as well as preserves Gauss integrality, with no degree or genus premise.',
        'Integral fraction witnesses give the exact diamond product and a nonzero reduced denominator.',
        'For every nonzero level M and prime p coprime to M, actual coordinate-degree preservation gives Gauss integrality of the original beta norm and residue equal to coefficient Frobenius of the arithmetic diamond image times q-to-q^p of the original residue. The matrix label is still p*d=1 modulo M.'],
    remaining='Actual original Gamma1 coordinate-degree equality and genus preservation remain open. Under both, the separately audited specialization/Kummer scope constructs a Picard map injective on every invertible torsion subgroup. Original norm/place/Picard compatibility, Tate Frobenius/inertia, parabolic arithmetic realization, all-weight association, automorphy and full higher continuation remain. 16/20; DUB17--20 OPEN.',
    externalBuild=False, externalImport=False, rootPinsChanged=False, proofLimitsChanged=False)
routefile = 'source-gamma-one-gauss-norm-audit-route-1357.json'
write(routefile, json.dumps(route, indent=2) + '\n')
s = (p / 'record_gamma_one_specialization_1334.py').read_text(encoding='utf-8')
for a, b in [('source-gamma-one-specialization-audit-route-1334', routefile[:-5]),
             ('source-gamma-one-specialization-1', stem), (old, new),
             ('ScratchOwnership1334', 'ScratchOwnership1357'),
             ('GAMMA ONE SPECIALIZATION', 'GAMMA ONE GAUSS NORM')]:
    s = s.replace(a, b)
s = s.replace('(6, 14, 28)', '(6, 8, 25)').replace('queries=14', 'queries=8')
s = s.replace('all 28 required', 'all 25 required').replace('requiredProofValueEdges=28', 'requiredProofValueEdges=25').replace('proofEdges=28', 'proofEdges=25')
ast.parse(s)
write('record_gamma_one_gauss_norm_1357.py', s)
s = (p / 'audit_gamma_one_specialization_1334.ps1').read_text(encoding='utf-8-sig')
for a, b in [(old, new), ('ScratchOwnership1334', 'ScratchOwnership1357'),
             ('record_gamma_one_specialization_1334', 'record_gamma_one_gauss_norm_1357')]:
    s = s.replace(a, b)
write('audit_gamma_one_gauss_norm_1357.ps1', s)
print(json.dumps(dict(modules=len(mods), queries=len(ths + defs), proofEdges=len(edges))))
