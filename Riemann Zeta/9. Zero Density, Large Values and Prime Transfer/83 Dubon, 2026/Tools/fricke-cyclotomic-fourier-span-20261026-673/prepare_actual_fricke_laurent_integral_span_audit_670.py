from pathlib import Path
import re,json,hashlib
p=Path(r'E:\Lean\.tmp\dubon83');repo=Path(r'E:\Lean\Riemann Zeta');prod=repo/'9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026/Extension/Dubon2026'
mods=['SourceLaurentIntegralCoefficientImage','SourceFrickeLaurentGeneratorIntegrality','SourceFrickeComplexFractionLaurent','SourceFrickeLaurentIntegralSpan']
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean');s=f.read_text(encoding='utf-8')
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 ns=re.search(r'^namespace (\S+)',s,re.M)[1]+'.'
 for k,n in re.findall(r'^(theorem|def) (\S+)',s,re.M):(ths if k=='theorem' else defs).append(ns+n)
assert (len(ths),len(defs))==(13,1),(len(ths),len(defs))
ns='Dubon2026.SourceFricke.';sf='Dubon2026.SourceFunctionField.'
roots=[ns+'exists_fricke_laurent_integral_span_of_principal_invariant']
extra=[ns+'exists_fraction_and_monic_j_of_principal_invariant',ns+'LevelGens.ring_monic_j_relation',sf+'represents_jqNModC',ns+'represents_frickeLaurentK',sf+'CuspTaylor.Represents.isIntegral_of_monic_relation',sf+'isIntegral_adjoin_of_isIntegral_coeffMap',ns+'ConstantDescent.mem_span_integral_generated_of_complex',sf+'IntegralJCoordinate.transcendental_qExpand_jqModC',sf+'CuspTaylor.Represents.ne_zero_of_function_ne_zero',sf+'CuspTaylor.Represents.cusp_of_mul_eq','IsIntegral.map_of_comp_eq']
required=ths+defs+extra
closure=set(mods);todo=mods.copy()
while todo:
 for imp in re.findall(r'^import (\w+)$',(p/(todo.pop()+'.lean')).read_text(encoding='utf-8'),re.M):
  if (p/(imp+'.lean')).exists() and imp not in closure:closure.add(imp);todo.append(imp)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=[],scratchImportClosure=sorted(closure),separateReason='All declarations are required by the consumer of the original holomorphic principal-level function and its actual modular orbit.')
def output(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-actual-fricke-laurent-integral-span-4-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,names in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(names),body)
body=body.replace('SOURCE ORIGINAL PRIMITIVE TATE RESTRICTION','SOURCE ACTUAL FRICKE LAURENT INTEGRAL SPAN').replace('Original Primitive Tate Restriction','Actual Fricke Laurent Integral Span')
output('SourceActualFrickeLaurentIntegralSpanAudit4.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceOriginalPrimitiveTateRestrictionDependencyAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,names in [('roots',roots),('localModules',sorted(closure)),('required',required)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(names),body)
body=body[:body.index('  logInfo m!')]+'''  logInfo m!"SOURCE ACTUAL FRICKE LAURENT INTEGRAL SPAN DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the original modular-function consumer. Only declaration values are traversed. Actual modular invariance and finite cusp poles supply the Fricke fraction and monic relation. Literal Laurent realization, derived generator integrality, existing expanded-j transcendence and the assembled constant descent give the ordinary complex integral span. Holomorphic summand recovery, rational Fourier spanning and arithmetic comparison remain; 16/20; DUB-17--20 OPEN."

#eval runPlanarPairingDependencyAudit
'''
output('SourceActualFrickeLaurentIntegralSpanDependencyAudit4.lean',imports+body)
reuse=[p/(m+'.lean') for m in ['SourceFrickeModularOrbitV2','SourceFrickeStableMonicV2','SourceFrickeCyclotomicLaurent','SourceCuspLaurentPolynomial','SourceFrickeCyclotomicFractionGerm','SourceCuspLaurentFractionIdentity','SourceLaurentIntegralConstantSpan']]
reuse+=[prod/(m+'.lean') for m in ['SourceLaurentIntegralDescent','SourceIntegralTranscendentalSeparability','SourceHolomorphicQuotientExtension','SourceMonicRelationRootBound']]
reuse+=[repo/'.lake/packages/mathlib/Mathlib/RingTheory/IntegralClosure/IsIntegral/Basic.lean']
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
route=dict(scope=670,chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> actual Gamma1 character realization -> Picard/H1 and full/parabolic/diamond comparison retaining the original homogeneous coefficient endomorphism -> actual differential/cusp comparison -> rational Fourier spanning -> integral base change of original Fricke functions.',
assumptionsToDischarge='For the original holomorphic principal-level function with finite cusp poles at every modular translate, derive a literal Laurent representation in the ordinary complex span of elements of the original cyclotomic j/Fricke field integral over its j-algebra. Actual modular-orbit fraction and monic relation are consumed. Generator integrality, finiteness, cyclotomic coefficients, j transcendence, complex fraction membership and all constant-descent premises are derived.',
remaining='The formal Laurent integral-span stage is proved for the actual function. Recover holomorphic functions for the integral Laurent summands, establish pole-cleared cyclotomic Fourier coefficients and rational Fourier spanning, then arbitrary Gamma1 differential realization and the remaining arithmetic association, automorphy and higher continuation chain. 16/20; DUB-17--20 OPEN.',
shorterRouteReview='Reuse the native finite-action monic polynomial instead of constructing a separate exact-degree Fricke orbit polynomial. Existing analytic Laurent representation and coefficient retraction give generator integrality. Native integral-equation transport maps it back to the original constant algebra. Reuse the already proved expanded-j transcendence; the alternate analytic fraction-field j-transcendence result is not needed on this Laurent route. The existing meromorphic germ identity handles denominator zeros. For the next holomorphic-recovery step, local SourceHolomorphicQuotientExtension and SourceMonicRelationRootBound already provide removable singularities and the monic-root bound, so importing the external general analytic quotient/valuation engine is unnecessary.',
reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],externalImport=False,externalFullClosureVerified=False,rootPinsChanged=False,proofLimitsChanged=False,modules=mods)
output('actual-fricke-laurent-integral-span-route-670.json',json.dumps(route,indent=2)+'\n')
print(json.dumps(dict(modules=len(mods),queries=len(ths+defs),theorems=len(ths),constructions=len(defs),edges=len(required))))