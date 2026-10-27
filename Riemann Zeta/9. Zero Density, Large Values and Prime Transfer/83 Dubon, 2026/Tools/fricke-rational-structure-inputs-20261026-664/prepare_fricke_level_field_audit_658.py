from pathlib import Path
import re,json
p=Path(r'E:\Lean\.tmp\dubon83')
mods=['SourceFrickePoleBounded','SourceFrickeHolomorphicAlgebra','SourceFrickeLevelAlgebra','SourceFrickeLevelGroup','SourceFrickeLevelField','SourceFrickeFixedFraction','SourceFrickeFixedFieldJ']
ns='Dubon2026.SourceFricke.'
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean')
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 s=re.sub(r'/\-.*?\-/','',f.read_text(encoding='utf-8'),flags=re.S)
 for k,n in re.findall(r'(?m)^(?:@\[[^\n]*?\]\s*)?(?:(?:local|scoped|noncomputable)\s+)*(lemma|theorem|def|abbrev|instance)(?:\s+\(priority := \d+\))?\s+([^\s({:]+)',s):
  (ths if k in ['lemma','theorem'] else defs).append(ns+n)
roots=[ns+'finrank_adjoin_j_levelField',ns+'mem_levelFixer_iff_pm']
separate=[ns+n for n in ['sl_smul_def','levelRing_coe_smul','levelGrp_mk_smul','fieldActionSMul','fieldMulAction','ringSelfDistribMulAction']]
required=[n for n in ths+defs if n not in separate]
extra=[ns+n for n in ['exists_polynomial_j_of_poleBounded_invariant','frickeF_faithful','mdifferentiable_frickeF','isBoundedAtImInfty_frickeF_mul_discriminant']]+['FixedPoints.finrank_eq_card','IsFractionRing.faithfulSMul','AnalyticOnNhd.eq_zero_or_eq_zero_of_mul_eq_zero']
required+=extra
closure=set(mods)
todo=mods.copy()
while todo:
 f=p/(todo.pop()+'.lean')
 for imp in re.findall(r'(?m)^import (\w+)$',f.read_text(encoding='utf-8')):
  if (p/(imp+'.lean')).exists() and imp not in closure:closure.add(imp);todo.append(imp)
closure=sorted(closure)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=separate,scratchImportClosure=closure,separateReason='Definitional presentations and local instance-selection aliases are independently axiom checked; no proof-value consumption is asserted for these names.')
def output(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-fricke-level-field-7-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,names in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(names),body)
body=body.replace('SOURCE ORIGINAL PRIMITIVE TATE RESTRICTION','SOURCE FRICKE LEVEL FIELD')
output('SourceFrickeLevelFieldAudit7.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceOriginalPrimitiveTateRestrictionDependencyAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,names in [('roots',roots),('localModules',closure),('required',required)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(names),body)
body=body[:body.index('  logInfo m!')]+'''  logInfo m!"SOURCE FRICKE LEVEL FIELD DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the actual Fricke fixed-field degree and stabilizer consumers. Only declaration values are traversed. The fixed subfield of the actual fraction field is exactly C(j), using actual cusp bounds, invariant polynomial reduction and a finite orbit denominator. The action kernel is exactly the principal congruence subgroup up to sign. Stable-family fraction realization, rational Fourier spanning, differential realization and arithmetic comparison remain; 16/20; DUB-17--20 OPEN."

#eval runPlanarPairingDependencyAudit
'''
output('SourceFrickeLevelFieldDependencyAudit7.lean',imports+body)
print(json.dumps(dict(modules=len(mods),queries=len(ths+defs),theorems=len(ths),constructions=len(defs),edges=len(required))))
