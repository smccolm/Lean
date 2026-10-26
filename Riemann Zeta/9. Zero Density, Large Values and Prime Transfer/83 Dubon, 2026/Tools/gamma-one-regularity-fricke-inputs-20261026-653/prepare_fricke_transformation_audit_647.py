from pathlib import Path
import re,json,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
mods=['SourceFrickePeriodHomothety','SourceFrickeModularLattice','SourceFrickeTorsionTransformation','SourceFrickeFunctionTransformation']
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean')
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime
 s=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',f.read_text(encoding='utf-8'),flags=re.S))
 ns='Dubon2026.SourceFricke.'
 ths += [ns+n for n in re.findall(r"^(?:@\[[^\n]*\]\s*)?(?:theorem|lemma) ([\w.']+)",s,re.M)]
 defs += [ns+n for n in re.findall(r"^(?:noncomputable\s+)?(?:def|abbrev) ([\w.']+)",s,re.M)]
roots=[ns+n for n in ['frickeF_hperm','frickeF_invariant_Gamma','frickeF_neg']]
extra=['PeriodPair.weierstrassP_add_coe','PeriodPair.weierstrassP_neg',"SlashInvariantForm.slash_action_eqn''"]
required=ths+defs+extra
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=[])
def output(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-fricke-transformation-4-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda ns:'#['+', '.join(chr(96)+n for n in ns)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,ns_ in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(ns_),body)
body=body.replace('SOURCE ORIGINAL PRIMITIVE TATE RESTRICTION','SOURCE FRICKE TRANSFORMATION')
output('SourceFrickeTransformationAudit4.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceOriginalPrimitiveTateRestrictionDependencyAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,ns_ in [('roots',roots),('localModules',mods),('required',required)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(ns_),body)
body=body[:body.index('  logInfo m!')]+'''  logInfo m!"SOURCE FRICKE TRANSFORMATION DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in actual Fricke transformation, principal-level invariance and sign consumers. Only declaration values are traversed. Holomorphy, Fourier structure, differential realization and the arithmetic comparison remain; 16/20; DUB-17--20 OPEN."

#eval runPlanarPairingDependencyAudit
'''
output('SourceFrickeTransformationDependencyAudit4.lean',imports+body)
print(json.dumps(dict(modules=4,queries=len(ths+defs),theorems=len(ths),constructions=len(defs),edges=len(required))))
