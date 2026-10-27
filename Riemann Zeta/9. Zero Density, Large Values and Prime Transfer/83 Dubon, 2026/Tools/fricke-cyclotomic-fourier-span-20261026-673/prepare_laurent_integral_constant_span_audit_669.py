from pathlib import Path
import re,json,hashlib
p=Path(r'E:\Lean\.tmp\dubon83');repo=Path(r'E:\Lean\Riemann Zeta');prod=repo/'9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026/Extension/Dubon2026'
mods=['SourceLaurentConstantTranscendence','SourceLaurentGeneratedConstants','SourceConstantExtensionChain','SourceConstantExtensionMonotonicity','SourceFiniteConstantIntegralCapture','SourceLaurentIntegralConstantSpan']
ns='Dubon2026.SourceFricke.ConstantDescent.'
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean');s=f.read_text(encoding='utf-8')
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 for k,n in re.findall(r'^(theorem|def) (\S+)',s,re.M):(ths if k=='theorem' else defs).append(ns+n)
assert (len(ths),len(defs))==(24,1),(len(ths),len(defs))
roots=[ns+'mem_span_integral_generated_of_complex']
extra=[ns+'mem_span_RSet_of_adjoin_simple',ns+'mem_span_RSet_of_adjoin_simple_transcendental',ns+'isIntegral_subalgebra_iff',ns+'mem_KFldT_iff','Submodule.span_induction','IntermediateField.adjoin_induction','Polynomial.eval'+chr(0x2082)+'_eq_sum_range','Dubon2026.SourceFunctionField.coeffMap_single','Dubon2026.SourceFunctionField.coeffMap_coeffMap']
required=ths+defs+extra
closure=set(mods);todo=mods.copy()
while todo:
 for imp in re.findall(r'^import (\w+)$',(p/(todo.pop()+'.lean')).read_text(encoding='utf-8'),re.M):
  if (p/(imp+'.lean')).exists() and imp not in closure:closure.add(imp);todo.append(imp)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=[],scratchImportClosure=sorted(closure),separateReason='Every retained declaration is required by the assembled Laurent integral-span consumer.')
def output(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-laurent-integral-constant-span-6-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,names in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(names),body)
body=body.replace('SOURCE ORIGINAL PRIMITIVE TATE RESTRICTION','SOURCE LAURENT INTEGRAL CONSTANT SPAN').replace('Original Primitive Tate Restriction','Laurent Integral Constant Span')
output('SourceLaurentIntegralConstantSpanAudit6.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceOriginalPrimitiveTateRestrictionDependencyAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,names in [('roots',roots),('localModules',sorted(closure)),('required',required)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(names),body)
body=body[:body.index('  logInfo m!')]+'''  logInfo m!"SOURCE LAURENT INTEGRAL CONSTANT SPAN DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the assembled complex integral-span consumer. Only declaration values are traversed. Finite constant capture and induction consume both proved simple-extension descents. Laurent coefficients derive relative transcendence, and the scalar-action bridge gives the ordinary coefficientwise complex span. Actual Fricke generator instantiation, holomorphic representative recovery and rational Fourier spanning remain; 16/20; DUB-17--20 OPEN."

#eval runPlanarPairingDependencyAudit
'''
output('SourceLaurentIntegralConstantSpanDependencyAudit6.lean',imports+body)
reuse=[p/'fricke-rational-descent-reuse-661/P2M/Sol/S_WLight_frickeFunction_intBaseChange.lean.txt',p/'SourceAlgebraicConstantIntegralSpan.lean',p/'SourceTranscendentalConstantIntegralSpanV2.lean',prod/'SourceLaurentScalarIndependence.lean',prod/'SourceLaurentCoefficientMap.lean',prod/'SourceIntegralTranscendentalSeparability.lean',repo/'.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean',repo/'.lake/packages/mathlib/Mathlib/LinearAlgebra/Span/Defs.lean',repo/'.lake/packages/mathlib/Mathlib/RingTheory/HahnSeries/PowerSeries.lean',repo/'.lake/packages/mathlib/Mathlib/RingTheory/HahnSeries/Multiplication.lean']
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
route=dict(scope=669,chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> actual finite Gamma1 character realization -> Picard/H1, full/parabolic and diamond comparison retaining the original homogeneous coefficient endomorphism -> actual differential/cusp comparison -> rational Fourier spanning -> Fricke integral base change -> finite constant-list integral-span assembly.',
assumptionsToDischarge='For a finite family of literal Laurent series over an original constant field, integral over its transcendental coordinate algebra, every element integral over the complex coordinate algebra in the complex generated field lies in the ordinary complex span of integral elements of the original generated field. Finite constant capture, both simple-extension descents, and their relative-transcendence conditions are proved and assembled. The two native scalar actions are compared explicitly.',
remaining='Actual j/Fricke generator membership, finite integral generator instantiation and its actual complex fraction Laurent realization are next. Holomorphic representative recovery and rational Fourier spanning, arbitrary Gamma1 differential realization and the arithmetic association/automorphy/higher continuation chain remain. 16/20; DUB-17--20 OPEN.',
shorterRouteReview='The existing literal Laurent coefficient map avoids a new analytic Fricke-field embedding and the external KPoleAt/holomorphic-domain machinery for relative transcendence. Taking a Laurent coefficient of a polynomial relation directly yields a polynomial over the original constants. The already proved scalar independence theorem was reviewed; its full basis-coordinate argument is unnecessary for this finite polynomial relation. Native adjoin induction captures the finite coefficient field, and the audited algebraic and transcendental steps replace all source shape assumptions. No incidental generic normalization theorem or proof-limit change is introduced. The existing expanded j-transcendence theorem will be reused for the actual instantiation.',
reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],sourceCommit='6e837e75355538c7f80bab5b956861e86c4eacc2',sourceLicense='Apache-2.0',externalImport=False,externalFullClosureVerified=False,rootPinsChanged=False,proofLimitsChanged=False,modules=mods)
output('laurent-integral-constant-span-route-669.json',json.dumps(route,indent=2)+'\n')
print(json.dumps(dict(modules=len(mods),queries=len(ths+defs),theorems=len(ths),constructions=len(defs),edges=len(required))))