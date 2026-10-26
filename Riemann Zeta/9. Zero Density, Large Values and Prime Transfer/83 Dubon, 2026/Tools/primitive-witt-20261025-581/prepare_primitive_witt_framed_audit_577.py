from pathlib import Path
import json,re,hashlib
p=Path(__file__).parent
prod=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
mods=['SourceResidualWittCoefficients','SourceResidualWittRepresentation','SourceResidualWittFramedRing','SourcePrimitiveWittFramedResidual']
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean')
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 s=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',f.read_text(encoding='utf-8'),flags=re.S))
 ns=re.search(r'^namespace (\S+)',s,re.M)[1]
 ths += [ns+'.'+n for n in re.findall(r"^theorem ([\w.']+)",s,re.M)]
 defs += [ns+'.'+n for n in re.findall(r"^(?:noncomputable\s+)?(?:def|abbrev) ([\w.']+)",s,re.M)]
roots=['Dubon2026.sourcePrimitive_exists_originalSupport_wittFramedResidualGalois_charP']
extra=['Dubon2026.sourcePrimitive_exists_originalSupport_finiteResidualGalois_charP','Dubon2026.SourceWittLift.residueMap','Dubon2026.SourceWittLift.witt_charZero','Dubon2026.arithmeticFramedUniversalRing_localData','Dubon2026.arithmeticFramedUniversalRepresentation_residue']
separate=['Dubon2026.sourceResidualWittResidueEquiv_residue']
required=list(dict.fromkeys([n for n in ths+defs if n not in separate]+extra))
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=separate)
def output(name,s):
 f=p/name;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-primitive-witt-framed-4-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda ns:'#['+', '.join(chr(96)+n for n in ns)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
template=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=template[template.index('private def runPlanarPairingAudit'):template.index('#lint in')]
for key,ns in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+key+r' : Array Name := #\[[^\n]*','let '+key+' : Array Name := '+arr(ns),body)
body=body.replace('SOURCE ORIGINAL PRIMITIVE TATE RESTRICTION','SOURCE PRIMITIVE WITT FRAMED')
output('SourcePrimitiveWittFramedAudit4.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
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
dep=dep[:dep.index('  logInfo m!')]+ '  logInfo m!"SOURCE PRIMITIVE WITT FRAMED DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the actual original all-weight residual framed consumer. Only declaration values are traversed. The actual finite residual coefficient field is identified with the residue field of its native characteristic-zero Witt ring. The same original residual matrices give the actual arithmetic framed deformation ring; its Noetherianity, maximal-ideal completeness and exact universal reduction to those matrices are derived. The original global cyclotomic determinant, real determinant, Fourier reductions and good-prime inertia remain in the same consumer. The constant-coefficient residue formula is separately axiom-checked as the exact coefficient bridge for the next fixed-determinant step. No characteristic-zero point of the deformation ring or all-weight adic association is asserted. Local/image/regularity properties, arithmetic automorphy and literal higher symmetric-power continuation remain open. 16/20; DUB-17--20 OPEN."\\n\\n#eval runPlanarPairingDependencyAudit\\n'
output('SourcePrimitiveWittFramedDependencyAudit4.lean',imports+dep)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
files=[prod/'SourceWittResidueLift.lean',prod/'ArithmeticFramedUniversalRing.lean',prod/'ArithmeticFixedDeterminantUniversality.lean',p/'SourcePrimitiveFiniteResidualGalois.lean']
math=Path(r'E:\Lean\Riemann Zeta\.lake\packages\mathlib\Mathlib')
files += [math/m for m in ['RingTheory/WittVector/DiscreteValuationRing.lean','RingTheory/WittVector/Complete.lean','RingTheory/LocalRing/ResidueField/Basic.lean','FieldTheory/Finite/Basic.lean']]
rd=dict(scope=577,chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> actual residual deformation problem -> native Witt coefficient ring and the original residual framed universal representation',reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in files],shorterRoute='Reuse native Witt DVR and completeness, SourceWittLift.residueMap, actual finite-field residual association and ArithmeticFramedUniversalRing. No second deformation representability proof, general coefficient-lift theory or unrelated p-divisible-group construction is introduced.',assumptionsToDischarge='Construct the native characteristic-zero Witt coefficient ring with precisely the original finite residue field. Derive Noetherianity and maximal-ideal completeness of the existing actual framed ring and literal equality of its universal reduction with the representation of the original all-weight form. All original local/global residual clauses remain. The constant-coefficient formula is separately checked and retained for the ensuing fixed-determinant compatibility proof.',remaining='A characteristic-zero Witt coefficient ring does not prove that the framed ring has characteristic zero or has a characteristic-zero point. All-weight adic association, required local/image/regularity properties, arithmetic automorphy and literal higher symmetric-power continuation remain required. The actual mixed-characteristic cyclotomic determinant lift is the next input to fixed-determinant deformation theory. 16/20; DUB-17--20 OPEN.',scratchImportClosure=localClosure,separatelyAxiomChecked=separate)
output('primitive-witt-framed-route-577.json',json.dumps(rd,indent=2)+'\\n')
print(json.dumps(dict(modules=len(mods),queries=len(cfg['queries']),theorems=len(ths),constructions=len(defs),edges=len(required))))
