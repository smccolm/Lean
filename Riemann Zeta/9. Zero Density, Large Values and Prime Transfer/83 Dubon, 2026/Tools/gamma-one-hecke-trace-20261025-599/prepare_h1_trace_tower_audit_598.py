from pathlib import Path
import json,re,hashlib
p=Path(__file__).parent
prod=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
mods=['SourceCoinducedTowerFunctions','SourceCoinducedTowerTrace','SourceShapiroH1Tower','SourceH1TraceTower']
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean')
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 s=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',f.read_text(encoding='utf-8'),flags=re.S))
 ns=re.search(r'^namespace (\S+)',s,re.M)[1]
 ths += [ns+'.'+n for n in re.findall(r"^theorem ([\w.']+)",s,re.M)]
 defs += [ns+'.'+n for n in re.findall(r"^(?:noncomputable\s+)?(?:def|abbrev) ([\w.']+)",s,re.M)]
roots=['Dubon2026.sourceHeckeH1Trace_tower']
extra=['Subgroup.quotientEquivProdOfLE','Subgroup.subgroupOfEquivOfLe','Dubon2026.originalCohomologyTrace_coinduced_lift','Dubon2026.OriginalShapiroRestriction.originalShapiroIso_eq_restriction_eval','Dubon2026.sourceHeckeH1Trace_eq_subgroupTrace','groupCohomology.map_comp']
separate=[]
required=list(dict.fromkeys([n for n in ths+defs if n not in separate]+extra))
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=separate)
def output(name,s):
 f=p/name;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-h1-trace-tower-4-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda ns:'#['+', '.join(chr(96)+n for n in ns)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
template=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=template[template.index('private def runPlanarPairingAudit'):template.index('#lint in')]
for key,ns in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+key+r' : Array Name := #\[[^\n]*','let '+key+' : Array Name := '+arr(ns),body)
body=body.replace('SOURCE ORIGINAL PRIMITIVE TATE RESTRICTION','SOURCE H1 TRACE TOWER')
output('SourceH1TraceTowerAudit4.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
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
dep=dep[:dep.index('  logInfo m!')]+ '  logInfo m!"SOURCE H1 TRACE TOWER DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the literal native H1 trace composition consumer. Only declaration values are traversed. The actual nested equivariant functions form a proved coefficient isomorphism; the native quotient-product equivalence reindexes the complete original finite coefficient trace. The existing Shapiro restriction/evaluation theorem proves the two-step native Shapiro comparison, and existing coefficient naturality then gives full native H1 trace composition. No trace-transitivity or Shapiro-composition premise is assumed. These results must still be combined with the actual Gamma1 Hecke base-change square and original coefficient action to prove surjective-transfer Hecke compatibility. Arithmetic geometry, Galois realization and higher continuation remain required. DUB-17--20 OPEN; 16/20."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceH1TraceTowerDependencyAudit4.lean',imports+dep)
route=p/'gamma1-transfer-trace-composition-route-598.json'
rd=json.loads(route.read_text(encoding='utf-8'))
assert 'scratchImportClosure' not in rd
rd['scratchImportClosure']=localClosure
route.write_text(json.dumps(rd,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(modules=len(mods),queries=len(cfg['queries']),theorems=len(ths),constructions=len(defs),edges=len(required))))
