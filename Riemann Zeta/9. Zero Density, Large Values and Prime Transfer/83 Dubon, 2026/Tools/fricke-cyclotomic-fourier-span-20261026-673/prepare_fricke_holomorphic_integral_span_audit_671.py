from pathlib import Path
import re,json,hashlib
p=Path(r'E:\Lean\.tmp\dubon83');repo=Path(r'E:\Lean\Riemann Zeta');prod=repo/'9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026/Extension/Dubon2026'
mods=['SourceMonicQuotientRelation','SourceHolomorphicMonicQuotient','SourceIntegralCoordinateMonic','SourceFrickeCyclotomicLaurentLifts','SourceFrickeClearedLaurentMonic','SourceFrickeIntegralHolomorphicRepresentative','SourceCuspLaurentSpan','SourceFrickeHolomorphicIntegralSpan']
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean');s=f.read_text(encoding='utf-8')
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 ns=re.search(r'^namespace (\S+)',s,re.M)[1]+'.'
 for k,n in re.findall(r'^(theorem|def) (\S+)',s,re.M):(ths if k=='theorem' else defs).append(ns+n)
assert (len(ths),len(defs))==(18,1),(len(ths),len(defs))
ns='Dubon2026.SourceFricke.';sf='Dubon2026.SourceFunctionField.'
roots=[ns+'mem_span_holomorphic_cyclotomic_fractions_of_principal_invariant']
extra=[ns+'exists_fricke_laurent_integral_span_of_principal_invariant',sf+'HolomorphicQuotient.exists_mdifferentiable_mul_eq',sf+'norm_le_of_monic_relation',sf+'CuspTaylor.Represents.eq_upperHalfPlane',sf+'CuspTaylor.Represents.cusp_of_mul_eq','IsFractionRing.div_surjective','CongruenceSubgroup.ModularGroup_T_pow_mem_Gamma']
required=ths+defs+extra
closure=set(mods);todo=mods.copy()
while todo:
 for imp in re.findall(r'^import (\w+)$',(p/(todo.pop()+'.lean')).read_text(encoding='utf-8'),re.M):
  if (p/(imp+'.lean')).exists() and imp not in closure:closure.add(imp);todo.append(imp)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=[],scratchImportClosure=sorted(closure),separateReason='Every declaration is used in the original holomorphic modular-function span consumer; generic machinery is limited to recovering these actual Fricke summands.')
def output(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-fricke-holomorphic-integral-span-8-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,names in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(names),body)
body=body.replace('SOURCE ORIGINAL PRIMITIVE TATE RESTRICTION','SOURCE FRICKE HOLOMORPHIC INTEGRAL SPAN').replace('Original Primitive Tate Restriction','Fricke Holomorphic Integral Span')
output('SourceFrickeHolomorphicIntegralSpanAudit8.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceOriginalPrimitiveTateRestrictionDependencyAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,names in [('roots',roots),('localModules',sorted(closure)),('required',required)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(names),body)
body=body[:body.index('  logInfo m!')]+'''  logInfo m!"SOURCE FRICKE HOLOMORPHIC INTEGRAL SPAN DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the original modular-function consumer. Only declaration values are traversed. The existing Laurent integral span supplies the summands; original cyclotomic function numerators and denominators, cleared monic relations, the native root bound and the existing removable extension derive their holomorphic representatives. The native complex scalar action and analytic identity principle give the actual function span. Pole-cleared cyclotomic Fourier coefficients, rational cusp spanning and arithmetic comparison remain; 16/20; DUB-17--20 OPEN."

#eval runPlanarPairingDependencyAudit
'''
output('SourceFrickeHolomorphicIntegralSpanDependencyAudit8.lean',imports+body)
reuse=[p/(m+'.lean') for m in ['SourceFrickeLaurentIntegralSpan','SourceCuspLaurentFunctionIdentity','SourceCuspLaurentFractionIdentity','SourceFrickeFractionPeriodicity','SourceFrickeCyclotomicFractionGerm']]
reuse+=[prod/(m+'.lean') for m in ['SourceHolomorphicQuotientExtension','SourceMonicRelationRootBound','SourceModularRatioGerms','SourceLaurentEuler']]
reuse+=[repo/'.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean',repo/'.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean']
# Intermediate-field localization is supplied by the existing imported Mathlib closure.
reuse=[f for f in reuse if f.exists()]
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
route=dict(scope=671,chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> actual Gamma1 character realization -> Picard/H1 and full/parabolic/diamond comparison retaining the original homogeneous coefficient endomorphism -> actual differential/cusp comparison -> rational Fourier spanning -> holomorphic realization of the integral Fricke Laurent summands.',assumptionsToDischarge='Derive actual holomorphic periodic cyclotomic Fricke fractions representing each integral Laurent summand, then lift the ordinary complex Laurent span to the actual principal-level holomorphic function. Neither holomorphic summand realization nor an actual cyclotomic spanning family is assumed.',remaining='The actual holomorphic function span is proved. Pole-cleared cyclotomic Fourier coefficients and rational cusp-form spanning remain, followed by arbitrary Gamma1 differential realization and the arithmetic association, automorphy and higher continuation chain. 16/20; DUB-17--20 OPEN.',shorterRouteReview='Before expanding the external analytic quotient development, reuse local SourceHolomorphicQuotientExtension, SourceMonicRelationRootBound and the native upper-half-plane identity theorem. They prove the required quotient extension directly from the cleared monic relation and continuity of its finitely many coefficients. Native IntermediateField fraction-ring surjectivity lifts the original Laurent fraction to actual cyclotomic numerator and denominator. Existing cusp-germ injectivity and coefficientwise scalar transport then lift the span. No general valuation engine, external analytic quotient file, new j transcendence proof, or incidental generalization is needed.',reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],externalImport=False,externalFullClosureVerified=False,rootPinsChanged=False,proofLimitsChanged=False,modules=mods)
output('fricke-holomorphic-integral-span-route-671.json',json.dumps(route,indent=2)+'\n')
print(json.dumps(dict(modules=len(mods),queries=len(ths+defs),theorems=len(ths),constructions=len(defs),edges=len(required))))