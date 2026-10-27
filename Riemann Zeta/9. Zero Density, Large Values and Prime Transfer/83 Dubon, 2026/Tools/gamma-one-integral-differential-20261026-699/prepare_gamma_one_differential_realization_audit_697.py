from pathlib import Path
import json, re, hashlib

p = Path(r'E:\Lean\.tmp\dubon83')
prod = Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
mods = ['SourceIntegerJEulerNormalization', 'SourceIntegerJEulerBaseChange',
 'SourceGammaOneIntegralCuspRatio', 'SourceGammaOneIntegralCuspLaurentSpan',
 'SourceGammaOneCuspDifferentialCoefficient', 'SourceGammaOneCuspDifferentialRealization']
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
assert (len(mods), len(ths), len(defs)) == (6, 8, 0)
sf = 'Dubon2026.SourceFunctionField.'
ns = sf + 'GammaOne.'
roots = [ns + 'exists_gammaOne_regular_differential_of_coefficients']
extra = [ns + 'gamma1_regular_of_diffQExp_matches_cusp',
 ns + 'functionFieldOver_eq_qExpFunctionFieldC', ns + 'div_mem_qExpFunctionFieldC',
 'Dubon2026.SourceFricke.span_gammaOne_weightTwo_integral_cuspForms_eq_top',
 sf + 'mem_span_of_coeffMap_mem_span', 'Dubon2026.SourceDifferential.diffQExp_smul_D',
 sf + 'ModularQDerivative.exists_qEuler_jqModC_formula']
required = ths + defs + extra
assert len(required) == len(set(required)) == 15
closure, todo = set(mods), mods.copy()
while todo:
 for imp in re.findall(r'^import (\w+)$', (p / (todo.pop() + '.lean')).read_text(encoding='utf-8'), re.M):
  if (p / (imp + '.lean')).exists() and imp not in closure:
   closure.add(imp)
   todo.append(imp)
cfg = dict(modules=mods, theorems=ths, constructions=defs, queries=ths+defs,
 proofEdges=required, roots=roots, separatelyAxiomChecked=[], scratchImportClosure=sorted(closure),
 separateReason='Every selected declaration serves actual regular-differential realization of every coefficient-field-valued weight-two Gamma1 cusp form at every nonzero level.')
def output(n, s):
 f = p / n
 assert not f.exists(), f
 f.write_text(s, encoding='utf-8')
output('source-gamma-one-cusp-differential-realization-6-audit-config.json', json.dumps(cfg, indent=2) + '\n')
arr = lambda names: '#[' + ', '.join(chr(96) + n for n in names) + ']'
imports = ''.join('import ' + m + '\n' for m in mods) + 'import Mathlib.Tactic\n\nopen Lean\n\n'
t = (p / 'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body = t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k, names in [('modules', mods), ('theorems', ths), ('constructions', defs)]:
 body = re.sub(r'let ' + k + r' : Array Name := #\[[^\n]*', lambda _: 'let ' + k + ' : Array Name := ' + arr(names), body)
body = body.replace('SOURCE ORIGINAL PRIMITIVE TATE RESTRICTION', 'SOURCE GAMMA ONE CUSP DIFFERENTIAL REALIZATION').replace('Original Primitive Tate Restriction', 'Gamma One Cusp Differential Realization')
output('SourceGammaOneCuspDifferentialRealizationAudit6.lean', imports + ''.join('#print axioms ' + n + '\n' for n in cfg['queries']) + '\n' + body + ''.join('#lint in ' + m + '\n' for m in mods))
t = (p / 'SourceOriginalPrimitiveTateRestrictionDependencyAudit8.lean').read_text(encoding='utf-8')
body = t[t.index('private def runPlanarPairingDependencyAudit'):]
for k, names in [('roots', roots), ('localModules', sorted(closure)), ('required', required)]:
 body = re.sub(r'let ' + k + r' : Array Name := #\[[^\n]*', lambda _: 'let ' + k + ' : Array Name := ' + arr(names), body)
body = body[:body.index('  logInfo m!')] + '''  logInfo m!"SOURCE GAMMA ONE CUSP DIFFERENTIAL REALIZATION DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in actual regular-differential realization. Only declaration values are traversed. Actual integral cusp spanning and coefficient retraction reduce the original cusp form to integral generators. Their equal-weight modular ratios and the proved nonzero integer j-derivative normalization construct the coefficient in the original field. The actual differential y D(j) has the original Fourier expansion, and the existing regularity theorem proves regularity at every place. The converse, original Hecke/diamond comparison and all arithmetic continuation obligations remain; 16/20; DUB-17--20 OPEN."

#eval runPlanarPairingDependencyAudit
'''
output('SourceGammaOneCuspDifferentialRealizationDependencyAudit6.lean', imports + body)
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest().upper()
oldroute = p / 'gamma-one-differential-realization-route-697.json'
old = json.loads(oldroute.read_text())
prior = p / 'source-gamma-one-integral-cusp-span-23-scratch-receipt.json'
assert sha(prior) == 'C18E5C8AF9E00AA65BFE91DC91F31025F8B1227985D4FBBB70CCD63B6C7A1E80'
route = dict(scope=697, chain=old['dependency'], modules=mods,
 assumptionsToDischarge='Every original Gamma1 weight-two cusp form with Fourier coefficients in the specified embedded characteristic-zero field has a differential in the original integral-ratio function field with exactly that Fourier expansion. For an algebraically closed coefficient field, the constructed differential is regular at every place. The only cusp-form coefficient premise is the source condition that its Fourier coefficients lie in the chosen field embedding. No matching differential, field-membership, integral relation or local regularity certificate remains as a premise.',
 remaining='The converse regular-differential-to-cusp construction remains. The actual Picard/H1, full/parabolic, transpose and diamond comparison must retain the original homogeneous coefficient endomorphism. Finite-character arithmetic realization, original all-weight characteristic-zero association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain. Full scope is unchanged; 16/20; DUB-17--20 OPEN.',
 shorterRouteReview=old['shorterRouteReview'] + ' Explicit source field algebra and the existing differential-expansion equality determine the differential witness without ambiguous scalar-action elaboration; proof limits remain unchanged.',
 reuseChecked=old['reuse'] + [dict(path=str(oldroute), sha256=sha(oldroute)), dict(path=str(prior), sha256=sha(prior))],
 externalImport=False, externalFullClosureVerified=False, rootPinsChanged=False, proofLimitsChanged=False)
output('gamma-one-cusp-differential-realization-audit-route-697.json', json.dumps(route, indent=2) + '\n')
print(json.dumps(dict(modules=6, queries=8, theorems=8, constructions=0, edges=15)))
