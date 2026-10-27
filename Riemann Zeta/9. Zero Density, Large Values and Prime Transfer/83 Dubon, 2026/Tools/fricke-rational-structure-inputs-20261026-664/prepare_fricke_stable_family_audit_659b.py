from pathlib import Path
import re,json
p=Path(r'E:\Lean\.tmp\dubon83')
mods=['SourceFrickeStableAlgebraV2','SourceFrickeStableGroupV2','SourceFrickeStableFieldV2','SourceFrickeStableEmbeddingV2','SourceFrickeStableFractionV2']
ns='Dubon2026.SourceFricke.'
ths=[];defs=[]
propInstances={'ring_isDomain','ring_smulCommClass','grp_smulCommClass','grp_faithful','grp_smulDistribClass','grpField_faithful','grpField_smulCommClass','scalarTowerField','scalarTowerRatJ'}
for m in mods:
 f=p/(m+'.lean')
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 s=re.sub(r'/\-.*?\-/','',f.read_text(encoding='utf-8'),flags=re.S)
 inside=False
 for line in s.splitlines():
  if line.strip()=='namespace LevelGens':inside=True
  if line.strip()=='end LevelGens':inside=False
  mt=re.match(r'^(?:@\[[^\n]*?\]\s*)?(?:(?:local|scoped|noncomputable)\s+)*(lemma|theorem|def|abbrev|structure|instance)(?:\s+\(priority := \d+\))?\s+([^\s({:]+)',line)
  if mt:
   k,n=mt.groups();full=ns+('LevelGens.' if inside else '')+n
   (ths if k in ['lemma','theorem'] or n in propInstances else defs).append(full)
roots=[ns+'exists_levelRing_frac']
separate=[ns+'LevelGens.'+n for n in ['ring_coe_smul','grp_mk_smul','coe_incl','fieldActionSMul','fieldMulAction','ringSelfDistribMulAction']]
required=[n for n in ths+defs if n not in separate]
extra=[ns+n for n in ['finrank_adjoin_j_levelField','mem_levelFixer_iff_pm','exists_fixed_div_of_fixed','eq_polynomial_j_of_invariant_of_mem_adjoin','HolFn.eq_zero_or_eq_zero_of_mul_eq_zero']]+['FixedPoints.finrank_eq_card','Module.finrank_mul_finrank']
required+=extra
closure=set(mods);todo=mods.copy()
while todo:
 f=p/(todo.pop()+'.lean')
 for imp in re.findall(r'(?m)^import (\w+)$',f.read_text(encoding='utf-8')):
  if (p/(imp+'.lean')).exists() and imp not in closure:closure.add(imp);todo.append(imp)
closure=sorted(closure)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=separate,scratchImportClosure=closure,separateReason='Definitional coercion presentations and local instance-selection aliases are independently axiom checked; no proof-value consumption is asserted for these names.')
def output(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-fricke-stable-family-5b-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,names in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(names),body)
body=body.replace('SOURCE ORIGINAL PRIMITIVE TATE RESTRICTION','SOURCE FRICKE STABLE FAMILY')
output('SourceFrickeStableFamilyAudit5b.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceOriginalPrimitiveTateRestrictionDependencyAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,names in [('roots',roots),('localModules',closure),('required',required)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(names),body)
body=body[:body.index('  logInfo m!')]+'''  logInfo m!"SOURCE FRICKE STABLE FAMILY DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the actual stable-family fraction consumer. Only declaration values are traversed. The original holomorphic function is a fraction in the actual Fricke algebra; finite cusp poles, modular stability and principal-level invariance suffice. Equality of the two actual fixed-field degrees makes the original inclusion surjective. Rational Fourier spanning, differential realization and arithmetic comparison remain; 16/20; DUB-17--20 OPEN."

#eval runPlanarPairingDependencyAudit
'''
output('SourceFrickeStableFamilyDependencyAudit5b.lean',imports+body)
print(json.dumps(dict(modules=len(mods),queries=len(ths+defs),theorems=len(ths),constructions=len(defs),edges=len(required))))
