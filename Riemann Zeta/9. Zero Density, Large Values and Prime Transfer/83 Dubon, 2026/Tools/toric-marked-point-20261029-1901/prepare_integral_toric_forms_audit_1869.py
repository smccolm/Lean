from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re, ast

p = Path(__file__).parent
repo = Path(r'E:\Lean\Riemann Zeta')
src = repo / '9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026/Extension/Dubon2026'
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
versions = [
    'SourceGammaOneTorsionWeightTwo1852c', 'SourceGammaOneTorsionFourierWidth1853a',
    'SourceGammaOneTorsionCoefficientFibers1855b', 'SourceGammaOneTorsionDivisorCoefficients1856b',
    'SourceToricFourierCharacter1857a', 'SourceToricFourierIntegralTransform1858a',
    'SourceToricFourierCoefficientPolynomials1859b', 'SourceGammaOneToricWeightTwo1861b',
    'SourceTateFourCoefficient1862a', 'SourceToricFourierIntegerFamilies1863a',
    'SourceGammaOneToricIntegralWeightTwo1864b', 'SourceGammaOneToricIntegralWeightFour1865b',
    'SourceGammaOneToricIntegralSlash1866b', 'SourceGammaOneToricSeriesReconstruction1867a',
    'SourceGammaOneIntegralToricInvariantForms1868b']
mapping = {v: re.sub(r'\d+[a-z]$', '', v) for v in versions}
modules = list(mapping.values())
base = 'Dubon2026.SourceFunctionField.'
tf = base + 'GammaOne.ToricFourier.'
forms = base + 'GammaOne.ToricForms.'
theorems, constructions, queries, files = [], [], [], []

def output(name, text):
    f = p / name
    assert not f.exists(), f
    if name.endswith('.py'): ast.parse(text)
    f.write_text(text, encoding='utf-8')

for v, m in mapping.items():
    f = p / (v + '.lean')
    assert f.with_suffix('.exit').read_text().strip() == '0'
    assert f.with_suffix('.log').stat().st_size == 0
    assert not (src / (m + '.lean')).exists()
    t = f.read_text(encoding='utf-8')
    for kind, name in re.findall(r'^(?!private )(?:(?:noncomputable|protected) )?(theorem|lemma|def|abbrev)\s+(\S+)', t, re.M):
        prefix = forms if v in versions[:4] else tf
        if m == 'SourceTateFourCoefficient' and name in ('tateA4', 'coeff_tateA4'): prefix = base
        full = prefix + name
        queries.append(full)
        (theorems if kind in ('theorem', 'lemma') else constructions).append(full)
    canon = re.sub(r'(?m)^import (\S+)$', lambda x: 'import ' + mapping.get(x[1], x[1]), t)
    assert re.sub(r'(?m)^import .*\n', '', canon) == re.sub(r'(?m)^import .*\n', '', t)
    output(m + '.lean', canon)
    files.append(dict(version=v, module=m, originalSha256=sha(f), canonicalSha256=sha(p / (m + '.lean')), bodyIdentical=True))
assert len(modules) == len(set(modules)) == 15
assert len(queries) == len(set(queries))

root = tf + 'exists_integralToricInvariantForms'
edges = [root]
edges += [forms + n for n in [
    'torsionWeightTwo', 'wpNormZ_slash_two', 'vecMulSL_zero_first', 'torsionWeightTwo_slash',
    'torsionWeightTwo_qExpansion_coeff', 'wpQCoeff_zero_first_product_fiber',
    'tsum_pnat_product_eq_divisor_sum', 'wpQCoeff_zero_first_divisor_sum']]
edges += [tf + n for n in [
    'W', 'W_slash', 'qExpansion_W_coeff', 'qExpansion_W', 'B', 'D',
    'isIntegralQExp_B', 'isIntegralQExp_D', 'qExpansion_B_coeff', 'qExpansion_D_coeff',
    'B_slash', 'D_slash', 'sum_reindex', 'det_mod', 'Fform', 'Fform_slash',
    'qExpansion_Fform', 'qExpansion_Fform_coeff', 'qExpansion_finset_sum',
    'aeval_wT', 'aeval_xT', 'inv_formula', 'one_sub_mul_S1', 'aeval_fT',
    'bZ_eq_sum', 'dZ_eq_sum', 'sum_ψ_bZ', 'sum_ψ_dZ', 'sum_filter_aeval',
    'sum_aeval', 'fourier_inversion', 'sum_ψ_mul', 'eisenstein4_map_eq',
    'weightTwo_series', 'weightFour_series']]
edges += ['Dubon2026.SourceFricke.' + n for n in [
    'mdifferentiable_wpNormZ', 'isBoundedAtImInfty_wpNormZ', 'wpNormZ_slash',
    'qExpansion_wpNormZ_coeff', 'qExpansion_coeff_width', 'finite_wpMonExp_fiber']]
edges += [base + 'qExpansion_E4_eq_map_eisenstein4', 'ModularForm.qExpansionAddHom',
          'SlashAction.sum_slash', 'AddChar.sum_mulShift', 'Nat.sum_divisorsAntidiagonal\'']
assert len(edges) == len(set(edges))
cfg = dict(modules=modules, theorems=theorems, constructions=constructions,
           queries=queries, roots=[root], proofEdges=edges,
           compileEvidence={m: m + '-1869' for m in modules}, separatelyAxiomChecked=[])
output('source-integral-toric-forms-1-audit-config.json', json.dumps(cfg, indent=2) + '\n')
output('integral-toric-forms-versions-1869.json', json.dumps(files, indent=2) + '\n')

imports = '\n'.join('import ' + m for m in modules) + '\nimport Mathlib.Tactic\n\nopen Lean\n\n'
array = lambda names: '#[' + ', '.join('`' + n for n in names) + ']'
def replace_array(t, name, names):
    t, count = re.subn(r'(?m)^  let ' + name + r' : Array Name := #\[.*$',
                      '  let ' + name + ' : Array Name := ' + array(names), t)
    assert count == 1, name
    return t

t = (p / 'SourceOriginalResidueCuspCountAudit2.lean').read_text(encoding='utf-8')
t = t[t.index('private def runOriginal'):t.index('\n#lint')]
t = t.replace('OriginalResidueCuspCount', 'IntegralToricForms').replace('Original residue cusp count', 'Integral toric forms').replace('SOURCE ORIGINAL RESIDUE CUSP COUNT', 'SOURCE INTEGRAL TORIC FORMS')
for name, vals in [('modules', modules), ('theorems', theorems), ('constructions', constructions)]:
    t = replace_array(t, name, vals)
t = imports + '\n'.join('#print axioms ' + n for n in queries) + '\n\n' + t
t += '\n' + '\n'.join('#lint in ' + m for m in modules) + '\n'
output('SourceIntegralToricFormsAudit1.lean', t)

t = (p / 'SourceOriginalResidueCuspCountDependencyAudit2.lean').read_text(encoding='utf-8')
t = t[t.index('private def runOriginal'):]
t = t.replace('OriginalResidueCuspCount', 'IntegralToricForms')
for name, vals in [('roots', [root]), ('localModules', modules), ('required', edges)]:
    t = replace_array(t, name, vals)
start = t.index('  logInfo m!')
stop = t.index('\n\n#eval', start)
t = t[:start] + '  logInfo m!"SOURCE INTEGRAL TORIC FORMS DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the VALUE closure of the actual integral toric invariant forms. Native analytic torsion forms, exact Fourier coefficients, integer polynomial transforms, actual E4 and the diamond action are consumed. Exact-order points, finite elliptic fibers and reverse genus remain open; DUB17--20 OPEN."' + t[stop:]
output('SourceIntegralToricFormsDependencyAudit1.lean', imports + t)

t = (p / 'SourceOriginalResidueCuspCountScratchOwnership1850.lean').read_text(encoding='utf-8')
t = t[t.index('private def inspectOwnership'):]
t = replace_array(t, 'mods', modules)
output('SourceIntegralToricFormsScratchOwnership1869.lean', imports + t)

route = json.loads((p / 'original-residue-finite-point-route-1852.json').read_text(encoding='utf-8'))
route['recordedUTC'] = datetime.now(timezone.utc).isoformat()
route['shorterRoute'] += (' The native qExpansionAddHom and SlashAction.sum_slash replace further finite-sum inductions. '
    'The Tate a4 coefficient series alone suffices for the quadratic invariant; Tate a6, ellipticity, '
    'non-toric slots and uniformization are deferred to the exact-order point obligation. '
    'The actual B and D forms, integer coefficients, exact Gamma0 action and literal Laurent identities are assembled without certificates.')
route['assumptionsToDischarge'] = [
    'Actual weight-two Gamma1 torsion modularity, holomorphy and all-cusp bounds are derived from native Weierstrass theorems.',
    'Exact width-one Fourier coefficients are obtained from native width conversion and finite exponent fibers, then finite divisor sums.',
    'Level-squared and level-fourth finite Fourier combinations construct actual weight-two B and weight-four D modular forms with explicit integer coefficients.',
    'The actual Gamma0 slash action is the dual index permutation by the upper-left entry; literal Laurent identities reconstruct both toric invariant series in every coefficient field admitting the prescribed primitive root.']
for name in ['SourceGammaOneFourierLinear', 'SourceGammaOneFunctionField', 'SourceModularNormPolynomial', 'SourceEisensteinFourExpansion']:
    f = src / (name + '.lean')
    route['reuseChecked'].append(dict(path=str(f), sha256=sha(f)))
for name in ['Mathlib/NumberTheory/LegendreSymbol/AddCharacter.lean', 'Mathlib/NumberTheory/ModularForms/QExpansion.lean', 'Mathlib/NumberTheory/ModularForms/SlashActions.lean', 'Mathlib/NumberTheory/Divisors.lean']:
    f = repo / '.lake/packages/mathlib' / name
    route['reuseChecked'].append(dict(path=str(f), sha256=sha(f)))
route['externalReferences'] = [dict(path=str(f), sha256=sha(f), built=False, imported=False) for f in [
    p / 'anthropic-toric-definitions-1851b/S_ModularCurve_exists_gamma1_isIntegralQExp_fourier_and_toricPoint_eq_sum.lean.txt',
    p / 'anthropic-tate-formal-1860b/Def_ModularCurve_TateFormal.lean.txt']]
route['boundary'] = 'The exact-order elliptic point and original-field marked-point correspondence are not assumed or claimed. This scope proves the integral invariant forms and literal series identities they will consume.'
output('source-integral-toric-forms-audit-route-1869.json', json.dumps(route, indent=2) + '\n')

build = "$ErrorActionPreference='Stop'\n$env:ELAN_HOME='C:\\Users\\Naraphim\\.elan'\n$env:LEAN_PATH='E:\\Lean\\.tmp\\dubon83'\n"
build += "Set-Location -LiteralPath '" + str(src.parent) + "'\n"
build += '$names=@(' + ','.join("'" + m + "'" for m in modules) + ')\n'
build += '''foreach($n in $names){
 $base="E:\Lean\.tmp\dubon83\$n-1869"
 if(Test-Path -LiteralPath "$base.log"){throw "Evidence exists: $n"}
 & 'C:\Users\Naraphim\.elan\bin\lake.exe' env lean -DautoImplicit=false -R 'E:\Lean\.tmp\dubon83' -o "E:\Lean\.tmp\dubon83\$n.olean" "E:\Lean\.tmp\dubon83\$n.lean" *> "$base.log"
 $rc=$LASTEXITCODE
 $rc | Out-File -LiteralPath "$base.exit" -Encoding ascii
 if($rc -ne 0 -or (Get-Item -LiteralPath "$base.log").Length -ne 0){Get-Content -LiteralPath "$base.log" -Encoding Unicode;exit 1}
 Write-Output "PASS: $n"
}
& powershell -NoProfile -ExecutionPolicy Bypass -File 'E:\Lean\.tmp\dubon83\audit_integral_toric_forms_1869.ps1'
exit $LASTEXITCODE
'''
output('build_integral_toric_forms_canonical_1869.ps1', build)
t = (p / 'audit_original_residue_cusp_count_1850.ps1').read_text(encoding='utf-8')
t = t.replace('SourceOriginalResidueCuspCountAudit2', 'SourceIntegralToricFormsAudit1').replace('SourceOriginalResidueCuspCountDependencyAudit2', 'SourceIntegralToricFormsDependencyAudit1').replace('SourceOriginalResidueCuspCountScratchOwnership1850', 'SourceIntegralToricFormsScratchOwnership1869').replace('record_original_residue_cusp_count_1850.py', 'record_integral_toric_forms_1869.py')
output('audit_integral_toric_forms_1869.ps1', t)

t = (p / 'record_original_residue_cusp_count_1850.py').read_text(encoding='utf-8')
replacements = {
    'source-original-residue-cusp-count-2': 'source-integral-toric-forms-1',
    'source-original-residue-cusp-count-audit-route-1850': 'source-integral-toric-forms-audit-route-1869',
    'SourceOriginalResidueCuspCountAudit2': 'SourceIntegralToricFormsAudit1',
    'SourceOriginalResidueCuspCountDependencyAudit2': 'SourceIntegralToricFormsDependencyAudit1',
    'SourceOriginalResidueCuspCountScratchOwnership1850': 'SourceIntegralToricFormsScratchOwnership1869',
    'SOURCE ORIGINAL RESIDUE CUSP COUNT': 'SOURCE INTEGRAL TORIC FORMS',
    '(12, 27, 38)': str((len(modules), len(queries), len(edges))),
    '== 12': '== 15', 'linterScopes=12': 'linterScopes=15',
    'all 38 required': 'all ' + str(len(edges)) + ' required',
    'requiredProofValueEdges=38': 'requiredProofValueEdges=' + str(len(edges)),
    'modules=12, queries=27': 'modules=15, queries=' + str(len(queries)),
    'proofEdges=38': 'proofEdges=' + str(len(edges))}
for a, b in replacements.items(): t = t.replace(a, b)
output('record_integral_toric_forms_1869.py', t)
print(json.dumps(dict(modules=len(modules), publicQueries=len(queries), publicTheorems=len(theorems), constructions=len(constructions), requiredValueEdges=len(edges), productionMutation=False)))
