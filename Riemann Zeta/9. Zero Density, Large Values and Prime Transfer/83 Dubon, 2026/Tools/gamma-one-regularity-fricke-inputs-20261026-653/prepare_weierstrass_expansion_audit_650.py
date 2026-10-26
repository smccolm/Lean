from pathlib import Path
import json,re
p=Path(r'E:\Lean\.tmp\dubon83')
mods=['SourceLipschitzTwo','SourceLipschitzTwoRealBoundary','SourceWeierstrassRowSeries','SourceWeierstrassLatticeRows','SourceWeierstrassTorsionExpansion','SourceWeierstrassTorsionTail','SourceWeierstrassTorsionHolomorphy','SourceFrickeHolomorphy']
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean')
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 s=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',f.read_text(encoding='utf-8'),flags=re.S))
 ns='Dubon2026.SourceFricke.'
 ths += [ns+n for n in re.findall(r"^(?:@\[[^\n]*\]\s*)?(?:theorem|lemma) ([\w.']+)",s,re.M)]
 defs += [ns+n for n in re.findall(r"^(?:noncomputable\s+)?(?:def|abbrev) ([\w.']+)",s,re.M)]
roots=[ns+'mdifferentiable_frickeF',ns+'weierstrassP_torsionPt_eq_tsum_prod']
# These are convenience identities used by the next coefficient model, not claimed to occur here.
separate=[ns+n for n in ['qN_ne_zero','summable_nat_mul_cexp_pow']]
extra=['EisensteinSeries.qExpansion_identity','PeriodPair.hasSum_weierstrassP','DifferentiableOn.analyticOnNhd','differentiableOn_tsum_of_summable_norm']
required=[n for n in ths+defs if n not in separate]+extra
closure=mods+['SourceFrickePeriodHomothetyV2','SourceFrickeModularLatticeV2','SourceFrickeTorsionTransformationV2','SourceFrickeFunctionTransformationV2']
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=separate,scratchImportClosure=closure)
def output(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-weierstrass-expansion-8-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda ns:'#['+', '.join(chr(96)+n for n in ns)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,ns_ in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(ns_),body)
body=body.replace('SOURCE ORIGINAL PRIMITIVE TATE RESTRICTION','SOURCE WEIERSTRASS EXPANSION')
output('SourceWeierstrassExpansionAudit8.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceOriginalPrimitiveTateRestrictionDependencyAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,ns_ in [('roots',roots),('localModules',closure),('required',required)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(ns_),body)
body=body[:body.index('  logInfo m!')]+'''  logInfo m!"SOURCE WEIERSTRASS EXPANSION DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the actual torsion expansion and Fricke holomorphy consumers. Only declaration values are traversed. Native Lipschitz summation, absolute lattice summability and locally uniform tail bounds justify the exact formula and holomorphy. Coefficient field, rational structure, differential realization and arithmetic comparison remain; 16/20; DUB-17--20 OPEN."

#eval runPlanarPairingDependencyAudit
'''
output('SourceWeierstrassExpansionDependencyAudit8.lean',imports+body)
print(json.dumps(dict(modules=8,queries=len(ths+defs),theorems=len(ths),constructions=len(defs),edges=len(required))))
