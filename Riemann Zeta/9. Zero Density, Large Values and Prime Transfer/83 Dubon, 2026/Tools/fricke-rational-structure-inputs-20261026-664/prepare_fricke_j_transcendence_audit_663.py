from pathlib import Path
import re,json,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
mods=['SourceFrickeJTranscendence']
ns='Dubon2026.SourceFricke.'
ths=[ns+n for n in ['analytic_j_aeval_injective','transcendental_analytic_j','transcendental_jA','transcendental_jK']]
defs=[]
roots=[ths[-1]]
extra=[ns+'aeval_j_apply','Dubon2026.SourceFunctionField.JMultiplicity.jf_surjective','Polynomial.funext','transcendental_algebraMap_iff']
required=ths+defs+extra
for m in mods:
 f=p/(m+'.lean')
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
closure=set(mods);todo=mods.copy()
while todo:
 f=p/(todo.pop()+'.lean')
 for imp in re.findall(r'(?m)^import (\w+)$',f.read_text(encoding='utf-8')):
  if (p/(imp+'.lean')).exists() and imp not in closure:closure.add(imp);todo.append(imp)
closure=sorted(closure)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=[],scratchImportClosure=closure,separateReason='All public mathematical declarations are required in actual proof values.')
def output(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-fricke-j-transcendence-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,names in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(names),body)
body=body.replace('SOURCE ORIGINAL PRIMITIVE TATE RESTRICTION','SOURCE FRICKE J TRANSCENDENCE')
output('SourceFrickeJTranscendenceAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceOriginalPrimitiveTateRestrictionDependencyAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,names in [('roots',roots),('localModules',closure),('required',required)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(names),body)
body=body[:body.index('  logInfo m!')]+'''  logInfo m!"SOURCE FRICKE J TRANSCENDENCE DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the actual Fricke-field j-transcendence consumer. Only declaration values are traversed. The existing surjectivity of actual analytic j gives injective polynomial evaluation. The actual algebra inclusion and its injective fraction-field map preserve transcendence. No cusp asymptotic reproof or transcendence premise is needed. Rational Fourier spanning, differential realization and arithmetic comparison remain; 16/20; DUB-17--20 OPEN."

#eval runPlanarPairingDependencyAudit
'''
output('SourceFrickeJTranscendenceDependencyAudit1.lean',imports+body)
print(json.dumps(dict(modules=len(mods),queries=len(ths+defs),theorems=len(ths),constructions=len(defs),edges=len(required))))
