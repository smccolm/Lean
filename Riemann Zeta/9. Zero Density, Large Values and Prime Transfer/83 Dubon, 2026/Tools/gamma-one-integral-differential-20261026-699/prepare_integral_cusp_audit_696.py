from pathlib import Path
import json, re, hashlib

p = Path(r'E:\Lean\.tmp\dubon83')
repo = Path(r'E:\Lean\Riemann Zeta')
prod = repo / '9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026/Extension/Dubon2026'
mods = json.loads((p / 'integral-cusp-selected-scope-696.json').read_text())['modules']
ths, defs = [], []
for m in mods:
 f = p / (m + '.lean')
 assert not (prod / f.name).exists(), m
 assert f.with_suffix('.exit').read_text().strip() == '0' and f.with_suffix('.log').stat().st_size == 0, m
 assert f.with_suffix('.olean').stat().st_mtime >= f.stat().st_mtime, m
 s = f.read_text(encoding='utf-8')
 ns = re.search(r'^namespace (\S+)', s, re.M)[1] + '.'
 for k, n in re.findall(r'^(theorem|def) (\S+)', s, re.M):
  (ths if k == 'theorem' else defs).append(ns + n)
assert (len(mods), len(ths), len(defs)) == (23, 55, 5)
ns, sf = 'Dubon2026.SourceFricke.', 'Dubon2026.SourceFunctionField.'
roots = [ns + 'span_gammaOne_weightTwo_integral_cuspForms_eq_top']
extra = [ns + 'span_gammaOne_rational_cuspForms_eq_top',
 ns + 'cuspWeightImage_mem_frickeSpan', ns + 'isIntegral_laurent_holomorphic_fraction',
 ns + 'exists_field_laurent_holomorphic_fraction',
 ns + 'exists_cyclotomic_function_fraction_of_laurent_field',
 sf + 'isIntegral_adjoin_of_isIntegral_coeffMap', sf + 'exists_coordinate_monic_relation',
 'Dubon2026.numberField_exists_positive_integral_multiple',
 'isIntegrallyClosed_of_isLocalization', 'LaurentSeries.of_powerSeries_localization',
 'Algebra.isIntegral_trace', 'trace_eq_sum_automorphisms']
required = ths + defs + extra
assert len(required) == len(set(required)) == 72
closure, todo = set(mods), mods.copy()
while todo:
 for imp in re.findall(r'^import (\w+)$', (p / (todo.pop() + '.lean')).read_text(encoding='utf-8'), re.M):
  if (p / (imp + '.lean')).exists() and imp not in closure:
   closure.add(imp)
   todo.append(imp)
cfg = dict(modules=mods, theorems=ths, constructions=defs, queries=ths+defs,
 proofEdges=required, roots=roots, separatelyAxiomChecked=[], scratchImportClosure=sorted(closure),
 separateReason='Every selected declaration serves the actual integral Fourier spanning of the full Gamma1 weight-two cusp-form space at every nonzero level.')
def output(n, s):
 f = p / n
 assert not f.exists(), f
 f.write_text(s, encoding='utf-8')
output('source-gamma-one-integral-cusp-span-23-audit-config.json', json.dumps(cfg, indent=2) + '\n')
arr = lambda names: '#[' + ', '.join(chr(96) + n for n in names) + ']'
imports = ''.join('import ' + m + '\n' for m in mods) + 'import Mathlib.Tactic\n\nopen Lean\n\n'
t = (p / 'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body = t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k, names in [('modules', mods), ('theorems', ths), ('constructions', defs)]:
 body = re.sub(r'let ' + k + r' : Array Name := #\[[^\n]*', lambda _: 'let ' + k + ' : Array Name := ' + arr(names), body)
body = body.replace('SOURCE ORIGINAL PRIMITIVE TATE RESTRICTION', 'SOURCE GAMMA ONE INTEGRAL CUSP SPAN').replace('Original Primitive Tate Restriction', 'Gamma One Integral Cusp Span')
output('SourceGammaOneIntegralCuspSpanAudit23.lean', imports + ''.join('#print axioms ' + n + '\n' for n in cfg['queries']) + '\n' + body + ''.join('#lint in ' + m + '\n' for m in mods))
t = (p / 'SourceOriginalPrimitiveTateRestrictionDependencyAudit8.lean').read_text(encoding='utf-8')
body = t[t.index('private def runPlanarPairingDependencyAudit'):]
for k, names in [('roots', roots), ('localModules', sorted(closure)), ('required', required)]:
 body = re.sub(r'let ' + k + r' : Array Name := #\[[^\n]*', lambda _: 'let ' + k + ' : Array Name := ' + arr(names), body)
body = body[:body.index('  logInfo m!')] + '''  logInfo m!"SOURCE GAMMA ONE INTEGRAL CUSP SPAN DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in actual weight-two Gamma1 integral Fourier spanning. Only declaration values are traversed. Actual rational cusp forms supply original Fricke membership and rational j-integrality; bounded original generators, normalized trace descent and native Laurent normality supply a uniform integer bound. Literal integral weight factors recover the original cusp series, and actual rational Fourier spanning gives integral spanning. Differential realization, Hecke and arithmetic comparison remain; 16/20; DUB-17--20 OPEN."

#eval runPlanarPairingDependencyAudit
'''
output('SourceGammaOneIntegralCuspSpanDependencyAudit23.lean', imports + body)
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
reuse = [p / 'laurent-denominator-reuse-route-695.json', p / 'bounded-denominator-reuse-assessment-690.json',
 p / 'integral-cusp-selected-scope-696.json', p / 'scratch-name-collision-restoration-verification-695.json']
route = dict(scope=696,
 chain=json.loads(reuse[0].read_text())['dependency'],
 assumptionsToDischarge='For actual Gamma1 cusp forms with rational width-one Fourier coefficients and explicit balance k+4a+6b=12m, derive original cyclotomic Fricke membership and rational j-integrality. Actual Fricke generators supply bounded fractions. Normalize a nonzero denominator coefficient and take the native cyclotomic trace to obtain a nonzero rational bounded fraction. Native Laurent localization and normality, after finite integer scaling of the monic relation, give a uniform integer bound. The original E4/E6 integer units and integral discriminant cancel the auxiliary weight factors, giving one integer multiple of the original cusp form with a literal integer Fourier series. The already proved full-space rational Fourier spanning then gives integral Fourier spanning; for weight two a=b=m=1, at every nonzero level.',
 remaining='Integral Fourier spanning is an inner obligation. Actual arbitrary Gamma1 cusp differential realization and its converse remain, followed by the original Picard/H1, full/parabolic, transpose and diamond comparison retaining the homogeneous coefficient endomorphism. Finite-character arithmetic realization, original all-weight characteristic-zero association, local/image/regularity, automorphy and literal higher symmetric-power continuation remain. No characteristic-zero lift is inferred from finite characters or deformation rings. All original twenty gates remain; 16/20; DUB-17--20 OPEN.',
 shorterRouteReview='The fixed-revision external bounded-denominator proof supplied the finite scaling pattern. Pinned Mathlib Laurent localization replaces its power-series fraction machinery and avoids separate pole-clearing exponents. Native trace-as-sum-of-automorphisms replaces a new convolution proof and the product of conjugate denominators. Existing original Laurent germ identity and coefficient retraction recover source function-field membership directly; existing integral E4, eta, j and torsion monomials provide the exact source generators. Four unused power-series-only development modules and one unused reverse helper are preserved as text and deferred. No general odd-weight balance theorem or alternative function-field model is introduced.',
 reuseChecked=[dict(path=str(f), sha256=sha(f)) for f in reuse], modules=mods,
 externalImport=False, externalFullClosureVerified=False, rootPinsChanged=False, proofLimitsChanged=False)
output('gamma-one-integral-cusp-span-route-696.json', json.dumps(route, indent=2) + '\n')
print(json.dumps(dict(modules=len(mods), queries=len(ths+defs), theorems=len(ths), constructions=len(defs), edges=len(required))))
