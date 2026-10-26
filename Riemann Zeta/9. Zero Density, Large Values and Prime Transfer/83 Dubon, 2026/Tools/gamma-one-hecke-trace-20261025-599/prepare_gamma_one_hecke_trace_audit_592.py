from pathlib import Path
import json,re,hashlib
p=Path(__file__).parent
prod=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
mods=['SourceGammaOneHeckeSubgroup', 'SourceGammaOneConstantHecke', 'SourceNativeCoinductionCosetTrace', 'SourceShapiroH1CocycleComparison', 'SourceShapiroH1CosetTrace', 'SourceGammaOneTransferCosetFormula', 'SourceGammaOneLiteralTransferSurjectivity']
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean')
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 s=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',f.read_text(encoding='utf-8'),flags=re.S))
 ns=re.search(r'^namespace (\S+)',s,re.M)[1]
 ths += [ns+'.'+n for n in re.findall(r"^theorem ([\w.']+)",s,re.M)]
 defs += [ns+'.'+n for n in re.findall(r"^(?:noncomputable\s+)?(?:def|abbrev) ([\w.']+)",s,re.M)]
roots=['Dubon2026.sourceGammaOne_literalTrace_surjective', 'Dubon2026.sourceGammaOneHeckeConjugation_matrix', 'Dubon2026.sourceGammaOneConstantHeckeH1_cocycle', 'Dubon2026.sourceGammaOneConstantHeckeCocycles_apply']
extra=['Dubon2026.sourceIntegralHeckeConjugate_matrix', 'Dubon2026.sourceHeckeUpper_finiteIndex', 'Dubon2026.sourceHeckeH1Trace_cocycle', 'Dubon2026.coinducedShapiroOne_evaluation_sub', 'Dubon2026.coinducedShapiroOne_mem_cocycles', 'Dubon2026.OriginalShapiroRestriction.originalShapiroIso_eq_restriction_eval', 'Dubon2026.sourceGammaOneConstantH1Transfer_surjective', 'Dubon2026.sourceGamma0H2_subsingleton', 'groupCohomology.coindIso', 'Rep.coindResAdjunction', 'Rep.coindToInd_apply', 'Dubon2026.originalCohomologyReindex']
separate=[]
required=list(dict.fromkeys([n for n in ths+defs if n not in separate]+extra))
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=separate)
def output(name,s):
 f=p/name;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-gamma-one-hecke-trace-7-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda ns:'#['+', '.join(chr(96)+n for n in ns)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
template=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=template[template.index('private def runPlanarPairingAudit'):template.index('#lint in')]
for key,ns in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+key+r' : Array Name := #\[[^\n]*','let '+key+' : Array Name := '+arr(ns),body)
body=body.replace('SOURCE ORIGINAL PRIMITIVE TATE RESTRICTION','SOURCE GAMMA ONE HECKE TRACE')
output('SourceGammaOneHeckeTraceAudit7.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
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
dep=dep[:dep.index('  logInfo m!')]+ '  logInfo m!"SOURCE GAMMA ONE HECKE TRACE DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the actual Gamma1 literal-transfer surjectivity and original diagonal-correspondence consumers. Only declaration values are traversed. The genuine Gamma1 subgroup and integral conjugation define the full native H1 correspondence. Existing explicit Shapiro cocycles and the proved homotopy identify the literal H1 trace with native Shapiro. The native finite-index coinduction counit equals the same coset trace by induction tensor evaluation and right/left coset inversion. The exact original Gamma1 transfer is that literal trace after the proved subgroup identification, and its surjectivity is derived from the existing original binary-module theorem. Transfer/Hecke-and-diamond compatibility, arithmetic geometric comparison and Galois realization remain required. DUB-17--20 OPEN; 16/20."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOneHeckeTraceDependencyAudit7.lean',imports+dep)
route=p/'gamma1-hecke-comparison-route-592.json'
rd=json.loads(route.read_text(encoding='utf-8'))
assert 'scratchImportClosure' not in rd
rd['scratchImportClosure']=localClosure
route.write_text(json.dumps(rd,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(modules=len(mods),queries=len(cfg['queries']),theorems=len(ths),constructions=len(defs),edges=len(required))))
