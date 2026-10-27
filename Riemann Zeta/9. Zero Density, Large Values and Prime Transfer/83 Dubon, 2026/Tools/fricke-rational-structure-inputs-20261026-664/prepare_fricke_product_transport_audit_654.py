from pathlib import Path
import re,json
p=Path(r'E:\Lean\.tmp\dubon83')
mods=['SourceQExpansionPeriodWidth','SourceEisensteinRationalSeries','SourceFrickeProductExpansion','SourceFrickeProductCyclotomic']
ths=[];defs=[];ns='Dubon2026.SourceFricke.'
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 s=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',f.read_text(encoding='utf-8'),flags=re.S))
 ths += [ns+n for n in re.findall(r"^(?:@\[[^\n]*\]\s*)?(?:theorem|lemma) ([\w.']+)",s,re.M)]
 defs += [ns+n for n in re.findall(r"^(?:noncomputable\s+)?(?:def|abbrev) ([\w.']+)",s,re.M)]
roots=[ns+n for n in ['qExpansion_frickeH_conj','qExpansion_frickeH_coeff_mem_kN','hasSum_qExpansion_frickeH']]
separate=[]
extra=['Dubon2026.hasSum_pow_dvd_reindex','EisensteinSeries.E_qExpansion_coeff','UpperHalfPlane.qExpansion_mul']+[ns+n for n in ['wpQSeriesK_map_inclusion','wpQSeriesK_map_cyclotomic']]
required=[n for n in ths+defs if n not in separate]+extra
closure=mods+json.loads((p/'source-fricke-cyclotomic-transport-3-audit-config.json').read_text())['scratchImportClosure']
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=separate,scratchImportClosure=closure,separateReason='No public theorem is exempted from the required actual proof-value traversal.')
def output(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-fricke-product-transport-4-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda ns:'#['+', '.join(chr(96)+n for n in ns)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,ns_ in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(ns_),body)
body=body.replace('SOURCE ORIGINAL PRIMITIVE TATE RESTRICTION','SOURCE FRICKE PRODUCT TRANSPORT')
output('SourceFrickeProductTransportAudit4.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceOriginalPrimitiveTateRestrictionDependencyAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,ns_ in [('roots',roots),('localModules',closure),('required',required)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(ns_),body)
body=body[:body.index('  logInfo m!')]+'''  logInfo m!"SOURCE FRICKE PRODUCT TRANSPORT DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the actual Fricke numerator coefficient and cyclotomic embedding consumers. Only declaration values are traversed. The native Eisenstein coefficient formula and existing sparse reindexing construct a rational prefactor; multiplication with the actual torsion series proves coefficient-field transport. Separation, rational spanning, differential realization and arithmetic comparison remain; 16/20; DUB-17--20 OPEN."

#eval runPlanarPairingDependencyAudit
'''
output('SourceFrickeProductTransportDependencyAudit4.lean',imports+body)
print(json.dumps(dict(modules=4,queries=len(ths+defs),theorems=len(ths),constructions=len(defs),edges=len(required))))
