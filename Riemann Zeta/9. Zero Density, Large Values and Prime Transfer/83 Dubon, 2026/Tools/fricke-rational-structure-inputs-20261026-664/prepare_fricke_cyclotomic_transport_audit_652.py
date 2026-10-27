from pathlib import Path
import re,json
p=Path(r'E:\Lean\.tmp\dubon83')
mods=['SourceFrickeCyclotomicCoefficients', 'SourceFrickeCyclotomicTransport', 'SourceFrickeTorsionConjugation']
ths=[];defs=[];ns='Dubon2026.SourceFricke.'
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 s=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',f.read_text(encoding='utf-8'),flags=re.S))
 ths += [ns+n for n in re.findall(r"^(?:@\[[^\n]*\]\s*)?(?:theorem|lemma) ([\w.']+)",s,re.M)]
 defs += [ns+n for n in re.findall(r"^(?:noncomputable\s+)?(?:def|abbrev) ([\w.']+)",s,re.M)]
roots=[ns+n for n in ['wpQSeriesK_map_inclusion','wpQSeriesK_map_cyclotomic']]
separate=[ns+n for n in ['coe_zetaK','coe_wpQCoeffK']]
extra=[ns+n for n in ['finite_wpMonExp_fiber','wpMonCoeff_mem_kN','wpQCoeff_mem_kN','qExpansion_wpNorm_coeff']]+['Complex.isPrimitiveRoot_exp']
required=[n for n in ths+defs if n not in separate]+extra
closure=mods+json.loads((p/'source-fricke-fourier-coefficients-7b-audit-config.json').read_text())['scratchImportClosure']
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=separate,scratchImportClosure=closure,separateReason='Two rfl identities expose the same native function definitions. They have explicit axiom checks; no named proof-value use is claimed when elaboration reduces those definitions.')
def output(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-fricke-cyclotomic-transport-3-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda ns:'#['+', '.join(chr(96)+n for n in ns)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,ns_ in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(ns_),body)
body=body.replace('SOURCE ORIGINAL PRIMITIVE TATE RESTRICTION','SOURCE FRICKE CYCLOTOMIC TRANSPORT')
output('SourceFrickeCyclotomicTransportAudit3.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceOriginalPrimitiveTateRestrictionDependencyAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,ns_ in [('roots',roots),('localModules',closure),('required',required)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(ns_),body)
body=body[:body.index('  logInfo m!')]+'''  logInfo m!"SOURCE FRICKE CYCLOTOMIC TRANSPORT DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the actual torsion Fourier coefficient-embedding consumers. Only declaration values are traversed. Native root-of-unity powers and finite exponent fibers transport the actual Fourier expansion to the transformed torsion coordinate. Fricke product transport, separation, rational spanning, differential realization and arithmetic comparison remain; 16/20; DUB-17--20 OPEN."

#eval runPlanarPairingDependencyAudit
'''
output('SourceFrickeCyclotomicTransportDependencyAudit3.lean',imports+body)
print(json.dumps(dict(modules=3,queries=len(ths+defs),theorems=len(ths),constructions=len(defs),edges=len(required))))
