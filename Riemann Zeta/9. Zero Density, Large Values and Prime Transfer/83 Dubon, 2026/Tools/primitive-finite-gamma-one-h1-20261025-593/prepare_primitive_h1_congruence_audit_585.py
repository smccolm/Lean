from pathlib import Path
import json,re,hashlib
p=Path(__file__).parent
prod=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
mods=['SourceFaithfulCharacterDivisibility','SourceBinaryH1PrimePowerKernel','SourcePrimitiveH1HeckeCongruence','SourcePrimitiveH1AdicOperatorKernel','SourcePrimitiveCongruentH1AdicRealization']
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean')
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 s=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',f.read_text(encoding='utf-8'),flags=re.S))
 ns=re.search(r'^namespace (\S+)',s,re.M)[1]
 ths += [ns+'.'+n for n in re.findall(r"^theorem ([\w.']+)",s,re.M)]
 defs += [ns+'.'+n for n in re.findall(r"^(?:noncomputable\s+)?(?:def|abbrev) ([\w.']+)",s,re.M)]
roots=['Dubon2026.sourcePrimitive_exists_congruentH1AdicRealization','Dubon2026.sourcePrimitiveH1Hecke_primePower_congruence_valuation']
extra=['Dubon2026.sourceFaithfulModule_nontrivial_characterFiber','isIntegral_of_smul_mem_submodule','Dubon2026.sourceSemilinearH1_exists_smul_of_zero','Dubon2026.sourceBinaryCoefficientMap_surjective','Dubon2026.sourceBinaryCoefficientMap_zmod_kernel','Dubon2026.sourceBinaryCoefficient_int_smul_injective','Dubon2026.sourceIntegralBinaryH1Finite','Dubon2026.sourceBinaryH1PrimeOperators_commute','Dubon2026.sourcePrimitive_exists_compatibleH1AdicRealization','Dubon2026.sourcePrimitiveFieldH1HeckeCharacter']
separate=[]
required=list(dict.fromkeys([n for n in ths+defs if n not in separate]+extra))
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=separate)
def output(name,s):
 f=p/name;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-primitive-h1-congruence-5-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda ns:'#['+', '.join(chr(96)+n for n in ns)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
template=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=template[template.index('private def runPlanarPairingAudit'):template.index('#lint in')]
for key,ns in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+key+r' : Array Name := #\[[^\n]*','let '+key+' : Array Name := '+arr(ns),body)
body=body.replace('SOURCE ORIGINAL PRIMITIVE TATE RESTRICTION','SOURCE PRIMITIVE H1 CONGRUENCE')
output('SourcePrimitiveH1CongruenceAudit5.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
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
dep=dep[:dep.index('  logInfo m!')]+ '  logInfo m!"SOURCE PRIMITIVE H1 CONGRUENCE DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the actual original primitive H1 congruence consumers. Only declaration values are traversed. The actual finite faithful Hecke-character fiber and native finite-lattice integrality criterion derive divisibility of original character values. The existing exact H1 kernel proof applies at every positive prime power. Actual operator vanishing implies zero under the same finite adic character. The original form supplies all local coefficient and compatibility data. Geometric Galois realization and characteristic-zero association remain required. DUB-17--20 OPEN; 16/20."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourcePrimitiveH1CongruenceDependencyAudit5.lean',imports+dep)
route=p/'primitive-h1-congruence-route-585.json'
rd=json.loads(route.read_text(encoding='utf-8'))
assert 'scratchImportClosure' not in rd
rd['scratchImportClosure']=localClosure
route.write_text(json.dumps(rd,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(modules=len(mods),queries=len(cfg['queries']),theorems=len(ths),constructions=len(defs),edges=len(required))))
