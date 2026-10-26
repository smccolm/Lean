from pathlib import Path
import json,re,hashlib
p=Path(__file__).parent
prod=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
mods=['SourceH1TraceIntersection', 'SourceGammaOneIntersectionTraceExchange', 'SourceGammaOneUpperH1Composition', 'SourceGammaOneSubgroupTraceHecke', 'SourceGammaOneTransferHecke']
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean')
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 s=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',f.read_text(encoding='utf-8'),flags=re.S))
 ns=re.search(r'^namespace (\S+)',s,re.M)[1]
 ths += [ns+'.'+n for n in re.findall(r"^theorem ([\w.']+)",s,re.M)]
 defs += [ns+'.'+n for n in re.findall(r"^(?:noncomputable\s+)?(?:def|abbrev) ([\w.']+)",s,re.M)]
roots=['Dubon2026.sourceGammaOneConstantH1Transfer_hecke']
extra=['Dubon2026.sourceGammaOneCoverBinaryHeckeTrace_pullback','Dubon2026.sourceGammaOneHeckeUpperTrace_reindex','Dubon2026.sourceGammaOneHeckeH1Pullback_square','Dubon2026.sourceGammaOneConstantH1Transfer_eq_trace','Dubon2026.sourceSubgroupH1Trace_tower','Dubon2026.originalCohomologyReindex_isIso','groupCohomology.map_comp','Dubon2026.sourceGammaOneCoverHeckeTraceSubgroup_eq','Dubon2026.sourceGammaOneSubgroupH1Iso']
separate=[]
required=list(dict.fromkeys([n for n in ths+defs if n not in separate]+extra))
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=separate)
def output(name,s):
 f=p/name;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-gamma-one-transfer-hecke-5-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda ns:'#['+', '.join(chr(96)+n for n in ns)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
template=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=template[template.index('private def runPlanarPairingAudit'):template.index('#lint in')]
for key,ns in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+key+r' : Array Name := #\[[^\n]*','let '+key+' : Array Name := '+arr(ns),body)
body=body.replace('SOURCE ORIGINAL PRIMITIVE TATE RESTRICTION','SOURCE GAMMA ONE TRANSFER HECKE')
output('SourceGammaOneTransferHeckeAudit5.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
localClosure=[];todo=mods.copy()
while todo:
 m=todo.pop()
 if m in localClosure:continue
 f=p/(m+'.lean')
 if not f.exists():continue
 localClosure.append(m)
 for line in re.findall(r'^import (.+)$',f.read_text(encoding='utf-8-sig'),re.M):
  for imp in line.split():
   if not imp.startswith(('Mathlib.','Dubon2026.','Lean.')) and (p/(imp+'.lean')).exists():todo.append(imp)
prior=(p/'SourceOriginalPrimitiveTateRestrictionDependencyAudit8.lean').read_text(encoding='utf-8')
dep=prior[prior.index('private def runPlanarPairingDependencyAudit'):]
for key,ns in [('roots',roots),('localModules',localClosure),('required',required)]:
 dep=re.sub(r'let '+key+r' : Array Name := #\[[^\n]*','let '+key+' : Array Name := '+arr(ns),dep)
dep=dep[:dep.index('  logInfo m!')]+ '  logInfo m!"SOURCE GAMMA ONE TRANSFER HECKE DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the actual original Gamma1 H1 transfer/Hecke commutation theorem. Only declaration values are traversed. The original native trace tower and existing group-cohomology isomorphism prove intersection trace exchange, instantiated on the exact original congruence groups. Actual upper-range composition, the audited native pullback square and upper-trace reindexing assemble the full correspondence square. The original literal-transfer formula identifies the resulting map with the already constructed transfer, retaining the homogeneous binary coefficient action at every coprime prime. No trace, compatibility, subgroup-preimage or coefficient-action premise remains. Arithmetic geometric and diamond comparison, finite Galois realization, original all-weight characteristic-zero association, automorphy and literal higher continuation remain required. DUB-17--20 OPEN; 16/20."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOneTransferHeckeDependencyAudit5.lean',imports+dep)
route=p/'gamma1-actual-transfer-hecke-route-611.json'
rd=json.loads(route.read_text(encoding='utf-8'))
assert 'scratchImportClosure' not in rd
rd['scratchImportClosure']=localClosure
route.write_text(json.dumps(rd,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(modules=len(mods),queries=len(cfg['queries']),theorems=len(ths),constructions=len(defs),edges=len(required))))
