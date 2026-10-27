from pathlib import Path
import re,json,hashlib
p=Path(r'E:\Lean\.tmp\dubon83');repo=Path(r'E:\Lean\Riemann Zeta');prod=repo/'9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026/Extension/Dubon2026'
mods=['SourceFrickeCyclotomicModularAction', 'SourceFrickeTwistModularEquivariance', 'SourceFrickeSpanMultiplication', 'SourceFrickePrincipalInvariance', 'SourceFrickeTwistPowers']
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean');s=f.read_text(encoding='utf-8')
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 ns=re.search(r'^namespace (\S+)',s,re.M)[1]+'.'
 for k,n in re.findall(r'^(theorem|def) (\S+)',s,re.M):(ths if k=='theorem' else defs).append(ns+n)
assert (len(ths),len(defs))==(14,3),(len(ths),len(defs))
ns='Dubon2026.SourceFricke.';sf='Dubon2026.SourceFunctionField.'
roots=[ns+'frickeCoefficientTwist_isZeroAtImInfty_sl_mul_discriminant_iff',ns+'frickeCoefficientTwist_pow',ns+'principalInvariant_frickeSpan']
extra=[ns+'smul_mem_levelGen',ns+'mdifferentiable_slFn',ns+'frickeF_invariant_Gamma',ns+'frickeCoefficientTwist_isZeroAtImInfty_mul_discriminant_iff',ns+'frickeCoefficientTwist_sum_original',ns+'frickeCoefficientTwist_fixes_original']
required=ths+defs+extra
closure=set(mods);todo=mods.copy()
while todo:
 for imp in re.findall(r'^import (\w+)$',(p/(todo.pop()+'.lean')).read_text(encoding='utf-8'),re.M):
  if (p/(imp+'.lean')).exists() and imp not in closure:closure.add(imp);todo.append(imp)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=[],scratchImportClosure=sorted(closure),separateReason='Every declaration is used by the actual all-cusps vanishing, power compatibility or principal invariance consumers required for elliptic divisibility transport.')
def output(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-fricke-twist-modular-algebra-5-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,names in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(names),body)
body=body.replace('SOURCE ORIGINAL PRIMITIVE TATE RESTRICTION','SOURCE FRICKE TWIST MODULAR ALGEBRA').replace('Original Primitive Tate Restriction','Fricke Twist Modular Algebra')
output('SourceFrickeTwistModularAlgebraAudit5.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceOriginalPrimitiveTateRestrictionDependencyAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,names in [('roots',roots),('localModules',sorted(closure)),('required',required)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(names),body)
body=body[:body.index('  logInfo m!')]+'''  logInfo m!"SOURCE FRICKE TWIST MODULAR ALGEBRA DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the actual all-cusps vanishing, power compatibility and principal invariance consumers. Only declaration values are traversed. Actual generator transformations prove modular stability and invariance; finite original scalar expansions prove multiplicativity and modular equivariance of the coefficient twist. Elliptic divisibility and cusp-subspace descent remain; 16/20; DUB-17--20 OPEN."

#eval runPlanarPairingDependencyAudit
'''
output('SourceFrickeTwistModularAlgebraDependencyAudit5.lean',imports+body)
reuse=[p/(m+'.lean') for m in ['SourceFrickeLevelAlgebraV3','SourceFrickeModularOrbitV2','SourceFrickeFractionPeriodicity','SourceFrickeTwistCuspVanishing','SourceFrickeCoefficientTwist']]
reuse += [repo/'.lake/packages/mathlib/Mathlib/Algebra/Algebra/Operations.lean',p/'gamma1-rational-structure-input-reuse-646/P2M/Sol/S_CuspForm_span_frickeRational_E4_pow_E6_pow_eq_top.lean.txt']
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
route={'scope':676,'chain':'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> actual Gamma1 character realization -> original Picard/H1, full/parabolic, transpose and diamond comparison -> actual differential/cusp comparison -> rational cusp-form spanning -> coefficient descent of the actual Fricke function span.','assumptionsToDischarge':'Prove that actual modular pullbacks preserve the original cyclotomic Fricke algebra, its holomorphic fractions and their complex span; prove coefficient twists commute with those pullbacks and preserve every translated cusp-vanishing condition. Prove multiplication and power compatibility from finite original scalar expansions. Derive principal-level invariance from original generator invariance and analytic cancellation of nonzero denominators, rather than assuming it.','remaining':'Transport holomorphic divisibility at elliptic points, then descend the actual cusp-form image. Arbitrary Gamma1 differential realization and the original finite-character arithmetic association, automorphy and higher continuation chain remain. 16/20; DUB-17--20 OPEN.','shorterRouteReview':'Before expanding the external function-twist algebra, reuse the already proved modular action, literal Fricke transformation law and native submodule multiplication. The existing actual coefficient twist is a linear equivalence, so addition and scalar compatibility require no new function extension. Finite original scalar sums prove multiplication and modular commutation directly. Analytic cancellation transfers principal-level invariance from each numerator and denominator; no separate modular-invariance input is added.','externalImport':False,'externalFullClosureVerified':False,'rootPinsChanged':False,'proofLimitsChanged':False}
route.update(reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],modules=mods)
output('fricke-twist-modular-algebra-route-676.json',json.dumps(route,indent=2)+'\n')
print(json.dumps(dict(modules=len(mods),queries=len(ths+defs),theorems=len(ths),constructions=len(defs),edges=len(required))))
