from pathlib import Path
import re,json,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
repo=Path(r'E:\Lean\Riemann Zeta')
prod=repo/'9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026/Extension/Dubon2026'
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
mods=['SourceCuspLaurentFunctionIdentity','SourceQExpansionLaurentWidth','SourcePoleBoundedCuspLaurent','SourceFrickeCyclotomicLaurent','SourceCuspLaurentPolynomial','SourceCuspLaurentFractionIdentity','SourceFrickeCyclotomicFractionGerm','SourceFrickeLaurentIntegralDescent','SourceFrickeFractionPeriodicity','SourceFrickeCyclotomicMonic']
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean');s=f.read_text(encoding='utf-8')
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 ns=re.search(r'^namespace (\S+)',s,re.M)[1]
 for match in re.finditer(r'^(theorem|def) (\S+)',s,re.M):
  prefix=ns+'.'
  if m=='SourceCuspLaurentFunctionIdentity' and match.start()>s.index('namespace CuspTaylor'):prefix+='CuspTaylor.'
  (ths if match[1]=='theorem' else defs).append(prefix+match[2])
assert (len(mods),len(ths),len(defs))==(10,39,3),(len(mods),len(ths),len(defs))
ns='Dubon2026.SourceFricke.'
roots=[ns+'exists_cyclotomic_monic_relation',ns+'exists_cusp_represents_of_poleBounded']
extra=['Dubon2026.SourceFunctionField.isIntegral_adjoin_of_isIntegral_coeffMap',
'Dubon2026.SourceFunctionField.CuspTaylor.Represents.eq_series',
'Dubon2026.SourceFunctionField.CuspTaylor.Represents.unique',
'Dubon2026.SourceFunctionField.CuspTaylor.represents_analytic',
'Dubon2026.SourceFunctionField.CuspTaylor.series_cuspFunction',
'Dubon2026.SourceFunctionField.CuspTaylor.eventually_ne_zero_of_series_ne_zero',
'Dubon2026.SourceFunctionField.qExpand_ofPowerSeries_eq_expand',
'Dubon2026.SourceFunctionField.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit',
'Dubon2026.SourceFunctionField.jqModC_eq_modular_quotient',
'Dubon2026.SourceFunctionField.coeffMap_ofPowerSeries',
'Dubon2026.SourceFunctionField.coeffMap_qExpand',
ns+'qExpansion_coeff_width',ns+'frickeHQSeriesK_map_inclusion',ns+'frickeF_mul_discriminant',
'UpperHalfPlane.mul_eq_zero_iff','AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq',
'Polynomial.monic_X_pow_add']
required=ths+defs+extra
closure=set(mods);todo=mods.copy()
while todo:
 f=p/(todo.pop()+'.lean')
 for imp in re.findall(r'(?m)^import (\w+)$',f.read_text(encoding='utf-8')):
  if (p/(imp+'.lean')).exists() and imp not in closure:closure.add(imp);todo.append(imp)
closure=sorted(closure)
def output(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=[],scratchImportClosure=closure,separateReason='All public mathematical declarations are required in the actual monic-descent consumer or the finite-cusp-pole realization needed by integral base change.')
output('source-fricke-cyclotomic-descent-10-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,names in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(names),body)
body=body.replace('SOURCE ORIGINAL PRIMITIVE TATE RESTRICTION','SOURCE FRICKE CYCLOTOMIC DESCENT').replace('Original Primitive Tate Restriction','Fricke Cyclotomic Descent')
output('SourceFrickeCyclotomicDescentAudit10.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceOriginalPrimitiveTateRestrictionDependencyAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,names in [('roots',roots),('localModules',closure),('required',required)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(names),body)
body=body[:body.index('  logInfo m!')]+'''  logInfo m!"SOURCE FRICKE CYCLOTOMIC DESCENT DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the actual cyclotomic monic-descent or finite-cusp-pole realization consumers. Only declaration values are traversed. The original Fricke fraction has a proved cyclotomic Laurent representation and derived periodicity. The existing coefficient retraction descends its complex monic j-relation, and analytic identity gives the cyclotomic relation for the original function. Integral spanning, rational Fourier structure, differential realization and arithmetic comparison remain; 16/20; DUB-17--20 OPEN."

#eval runPlanarPairingDependencyAudit
'''
output('SourceFrickeCyclotomicDescentDependencyAudit10.lean',imports+body)
local=['SourceMeromorphicLaurentRealization','SourceCuspMeromorphicGerms','SourceTaylorQuotientGerms','SourceOriginalJCuspGerm','SourceLaurentIntegralDescent','SourceLaurentScalarIndependence','SourceIntegralPowerSeriesFrobenius','SourceJModularQuotient','SourceDiscriminantIntegralExpansion','SourceHasseCoefficientTransport','SourceLaurentCoefficientReindex']
reuse=[prod/(m+'.lean') for m in local]+[p/(m+'.lean') for m in ['SourceFrickeProductCyclotomic','SourceFrickeCuspInputs','SourceFrickeModularOrbitV2','SourceQExpansionPeriodWidth']]
reuse += [p/'fricke-rational-descent-reuse-661/P2M/Sol/S_WLight_exists_monicRel_j_K_of_mdifferentiable_frickeQuotient.lean.txt']
reuse += [repo/'.lake/packages/mathlib/Mathlib/Analysis/Complex/UpperHalfPlane/Manifold.lean',repo/'.lake/packages/mathlib/Mathlib/Analysis/Analytic/Uniqueness.lean']
route=dict(scope=665,chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> actual finite Gamma1 character realization -> Picard/H1, full/parabolic and diamond comparison preserving the original homogeneous coefficient endomorphism -> actual differential/cusp comparison -> cyclotomic rational Fourier spanning -> integral base change of Fricke fractions -> cyclotomic monic relations.',
assumptionsToDischarge='For an actual holomorphic fraction F*b=a with a,b in the original cyclotomic j/Fricke algebra and b nonzero, a supplied actual complex monic j-relation descends to an actual monic relation with coefficients in the cyclotomic field. The cyclotomic Laurent representation and periodicity are derived, not assumed. The literal substituted j-series is identified with the original analytic j at width N. Actual periodic holomorphic functions with finite cusp poles have Laurent representations.',
remaining='The input complex monic relation is explicit; the prior modular-orbit theorem supplies it under actual principal-level invariance and finite cusp-pole hypotheses. Integral base-change spanning, rational Fourier spanning, arbitrary Gamma1 cusp differential realization and the converse remain. Picard/H1, full/parabolic/transpose/diamond, Frobenius/inertia and original all-weight arithmetic association, automorphy and literal higher continuation remain. 16/20; DUB-17--20 OPEN.',
route='Reuse the existing meromorphic cusp-germ field operations and uniqueness, native analytic identity/domain theorems, integral discriminant coefficients, the existing width formula and Laurent reindexing, and the already proved coefficient-linear-retraction descent. A duplicate reindex proof was removed before audit in favor of SourceIntegralPowerSeriesFrobenius. This replaces the selected external monic-coefficient proof route without importing its large linear-system and Fourier flatness machinery or increasing limits. Integral constant-extension spanning is a separate unresolved step; no characteristic-zero Hecke lift is inferred. All final sources receive a fresh sequential rebuild before auditing.',
reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],externalSourceCommit='6e837e75355538c7f80bab5b956861e86c4eacc2',externalSourceLicense='Apache-2.0',externalImport=False,externalFullClosureVerified=False,rootPinsChanged=False,proofLimitsChanged=False)
output('fricke-cyclotomic-descent-local-reuse-route-665.json',json.dumps(route,indent=2)+'\n')
print(json.dumps(dict(modules=len(mods),queries=len(ths+defs),theorems=len(ths),constructions=len(defs),edges=len(required))))