from pathlib import Path
import re,json
p=Path(r'E:\Lean\.tmp\dubon83')
mods=['SourceConstantExtensionIntegralAlgebra','SourceAlgebraicConstantRoots','SourceAlgebraicConstantLift','SourceAlgebraicConstantInterpolation','SourceAlgebraicConstantIntegralSpan']
ns='Dubon2026.SourceFricke.ConstantDescent.'
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean');s=f.read_text(encoding='utf-8')
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 for k,n in re.findall(r'^(theorem|abbrev|def) (\S+)',s,re.M):
  (ths if k=='theorem' else defs).append(ns+n)
assert (len(ths),len(defs))==(14,3),(len(ths),len(defs))
roots=[ns+'mem_span_RSet_of_adjoin_simple']
extra=['Lagrange.eq_interpolate_of_eval_eq','Polynomial.degree_sum_fin_lt','IntermediateField.algHomAdjoinIntegralEquiv','IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen','IntermediateField.adjoin.powerBasis','IsIntegral.sum','IsIntegral.mul','minpoly.dvd','PerfectField.separable_of_irreducible']
required=ths+defs+extra
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=[],scratchImportClosure=mods,separateReason='All mathematical declarations are required in the algebraic constant-adjoining integral-span consumer.')
def output(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-algebraic-constant-integral-span-5-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,names in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(names),body)
body=body.replace('SOURCE ORIGINAL PRIMITIVE TATE RESTRICTION','SOURCE ALGEBRAIC CONSTANT INTEGRAL SPAN').replace('Original Primitive Tate Restriction','Algebraic Constant Integral Span')
output('SourceAlgebraicConstantIntegralSpanAudit5.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceOriginalPrimitiveTateRestrictionDependencyAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,names in [('roots',roots),('localModules',mods),('required',required)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(names),body)
body=body[:body.index('  logInfo m!')]+'''  logInfo m!"SOURCE ALGEBRAIC CONSTANT INTEGRAL SPAN DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the algebraic constant-adjoining consumer. Only declaration values are traversed. Separable finite extension embeddings and Lagrange interpolation derive integral coordinates over the original constants. The transcendental constant step, finite constant-list induction, actual Fricke-field instantiation, rational Fourier spanning and remaining arithmetic chain are open; 16/20; DUB-17--20 OPEN."

#eval runPlanarPairingDependencyAudit
'''
output('SourceAlgebraicConstantIntegralSpanDependencyAudit5.lean',imports+body)
print(json.dumps(dict(modules=len(mods),queries=len(ths+defs),theorems=len(ths),constructions=len(defs),edges=len(required))))