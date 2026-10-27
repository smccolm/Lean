from pathlib import Path
import re,json
p=Path(r'E:\Lean\.tmp\dubon83')
mods=['SourceLaurentAnalyticPolynomial','SourceLevelOneAnalyticJPolynomial','SourceInvariantAnalyticJPolynomial']
ns='Dubon2026.SourceFunctionField.'
fr='Dubon2026.SourceFricke.'
ths=[ns+n for n in ['RealL.pow','RealL.aeval','realL_qExpansion','realL_jqModC','exists_levelOne_analytic_j_polynomial']]+[fr+n for n in ['poleClearedLevelOne_apply','exists_polynomial_j_of_poleBounded_invariant']]
defs=[fr+'poleClearedLevelOne']
for m in mods:
 f=p/(m+'.lean')
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
roots=[fr+'exists_polynomial_j_of_poleBounded_invariant']
separate=[]
extra=[ns+n for n in ['exists_levelOne_j_polynomial','RealL.mul','realL_jqC','jqModC_eq_modular_quotient']]+['UpperHalfPlane.hasSum_qExpansion','ModularForm.mul_slash_SL2']
required=ths+defs+extra
closure=mods
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=separate,scratchImportClosure=closure,separateReason='All public mathematical declarations are required in actual proof values.')
def output(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-level-one-analytic-polynomial-3-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda ns:'#['+', '.join(chr(96)+n for n in ns)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,ns_ in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(ns_),body)
body=body.replace('SOURCE ORIGINAL PRIMITIVE TATE RESTRICTION','SOURCE LEVEL ONE ANALYTIC POLYNOMIAL')
output('SourceLevelOneAnalyticPolynomialAudit3.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceOriginalPrimitiveTateRestrictionDependencyAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,ns_ in [('roots',roots),('localModules',closure),('required',required)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(ns_),body)
body=body[:body.index('  logInfo m!')]+'''  logInfo m!"SOURCE LEVEL ONE ANALYTIC POLYNOMIAL DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the actual invariant-polynomial consumer. Only declaration values are traversed. The existing exact level-one Laurent polynomial reduction is transferred through actual convergent expansions and products. Clearing the finite cusp pole yields a genuine modular form and a degree-bounded polynomial in the actual analytic j. Fricke fixed fractions, rational spanning, differential realization and arithmetic comparison remain; 16/20; DUB-17--20 OPEN."

#eval runPlanarPairingDependencyAudit
'''
output('SourceLevelOneAnalyticPolynomialDependencyAudit3.lean',imports+body)
print(json.dumps(dict(modules=3,queries=len(ths+defs),theorems=len(ths),constructions=len(defs),edges=len(required))))
