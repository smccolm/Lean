from pathlib import Path
import re,json,hashlib
p=Path(r'E:\Lean\.tmp\dubon83');repo=Path(r'E:\Lean\Riemann Zeta');prod=repo/'9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026/Extension/Dubon2026'
mods=['SourceMeromorphicCuspPoleClearing','SourceFrickePoleClearedFourierSpan']
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean');s=f.read_text(encoding='utf-8')
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 ns=re.search(r'^namespace (\S+)',s,re.M)[1]+'.'
 for k,n in re.findall(r'^(theorem|def) (\S+)',s,re.M):(ths if k=='theorem' else defs).append(ns+n)
assert (len(ths),len(defs))==(6,1),(len(ths),len(defs))
ns='Dubon2026.SourceFricke.';sf='Dubon2026.SourceFunctionField.'
roots=[ns+'mem_span_pole_cleared_cyclotomic_of_principal_invariant']
extra=[ns+'exists_cyclotomic_fraction_represents',ns+'mem_span_holomorphic_cyclotomic_fractions_of_principal_invariant',sf+'CuspTaylor.Represents.meromorphicAt',sf+'CuspTaylor.Represents.eq_series',ns+'coeffMap_discriminantLaurentK','tendsto_nhds_of_meromorphicOrderAt_nonneg','tendsto_zero_iff_meromorphicOrderAt_pos']
required=ths+defs+extra
closure=set(mods);todo=mods.copy()
while todo:
 for imp in re.findall(r'^import (\w+)$',(p/(todo.pop()+'.lean')).read_text(encoding='utf-8'),re.M):
  if (p/(imp+'.lean')).exists() and imp not in closure:closure.add(imp);todo.append(imp)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=[],scratchImportClosure=sorted(closure),separateReason='Every declaration is used in the original pole-cleared cyclotomic Fourier span consumer.')
def output(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-fricke-pole-cleared-fourier-span-2-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,names in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(names),body)
body=body.replace('SOURCE ORIGINAL PRIMITIVE TATE RESTRICTION','SOURCE FRICKE POLE CLEARED FOURIER SPAN').replace('Original Primitive Tate Restriction','Fricke Pole Cleared Fourier Span')
output('SourceFrickePoleClearedFourierSpanAudit2.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceOriginalPrimitiveTateRestrictionDependencyAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,names in [('roots',roots),('localModules',sorted(closure)),('required',required)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(names),body)
body=body[:body.index('  logInfo m!')]+'''  logInfo m!"SOURCE FRICKE POLE CLEARED FOURIER SPAN DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the original modular-function consumer. Only declaration values are traversed. The existing actual holomorphic function span supplies the summands. Meromorphic cusp order and the positive discriminant order derive a clearing power. Existing cyclotomic Laurent representations and analytic series uniqueness prove every Fourier coefficient belongs to the original cyclotomic field. Rational cusp spanning and arithmetic comparison remain; 16/20; DUB-17--20 OPEN."

#eval runPlanarPairingDependencyAudit
'''
output('SourceFrickePoleClearedFourierSpanDependencyAudit2.lean',imports+body)
reuse=[p/(m+'.lean') for m in ['SourceFrickeHolomorphicIntegralSpan','SourceFrickeCyclotomicFractionGerm','SourceFrickeCyclotomicLaurent','SourcePoleBoundedCuspLaurent','SourceCuspLaurentFunctionIdentity']]
reuse += [prod/(m+'.lean') for m in ['SourceCuspDiscRealization','SourceQuotientCuspGrowth','SourceQuotientCuspPoleBound']]
reuse += [repo/'.lake/packages/mathlib/Mathlib/Analysis/Meromorphic/Order.lean',repo/'.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/QExpansion.lean']
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
route={'scope': 672, 'chain': 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> actual Gamma1 character realization -> Picard/H1 and full/parabolic/diamond comparison retaining the original homogeneous coefficient endomorphism -> actual differential/cusp comparison -> rational cusp-form spanning -> pole-cleared cyclotomic Fourier span.', 'assumptionsToDischarge': 'For every actual holomorphic cyclotomic Fricke fraction, derive a discriminant power clearing the cusp pole and prove that every resulting Fourier coefficient belongs to the original cyclotomic field. Thus the actual principal-level holomorphic function is in the complex span of functions with these proved Fourier properties. No finite-pole bound, Fourier coefficient membership or monic-growth premise is assumed for the summands.', 'remaining': 'Rational cusp-form spanning still requires the modular-weight, cusp and coefficient-descent steps; the pole-cleared weight-zero function span alone does not construct an arbitrary Gamma1 differential. Actual Picard/H1 and finite-character comparison, original all-weight arithmetic association, automorphy and higher continuation remain. 16/20; DUB-17--20 OPEN.', 'shorterRouteReview': 'Review the already proved SourceCuspDiscRealization and the local quotient-growth modules before expanding the external Fourier division development. Native meromorphic-order positivity for the discriminant and the native nonnegative-order limit theorem clear the pole directly. The existing cyclotomic Laurent fraction and discriminant representations, together with uniqueness of the analytic Laurent series, then give coefficient membership directly. This removes the external recursive power-series division and monic-growth development from the required route.', 'externalImport': False, 'externalFullClosureVerified': False, 'rootPinsChanged': False, 'proofLimitsChanged': False}
route.update(reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],modules=mods)
output('fricke-pole-cleared-fourier-span-route-672.json',json.dumps(route,indent=2)+'\n')
print(json.dumps(dict(modules=len(mods),queries=len(ths+defs),theorems=len(ths),constructions=len(defs),edges=len(required))))