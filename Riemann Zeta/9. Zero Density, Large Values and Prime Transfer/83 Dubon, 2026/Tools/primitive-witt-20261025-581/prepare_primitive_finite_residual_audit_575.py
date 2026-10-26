from pathlib import Path
import json,re,hashlib
p=Path(__file__).parent
prod=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
mods=['SourceFiniteResidualCoefficientField','SourceResidualCoefficientDeterminant','SourceFiniteResidualArithmeticDescent','SourcePrimitiveFiniteResidualGalois']
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean')
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 s=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',f.read_text(encoding='utf-8'),flags=re.S))
 ns=re.search(r'^namespace (\S+)',s,re.M)[1]
 ths += [ns+'.'+n for n in re.findall(r"^theorem ([\w.']+)",s,re.M)]
 defs += [ns+'.'+n for n in re.findall(r"^(?:noncomputable\s+)?(?:def|abbrev) ([\w.']+)",s,re.M)]
roots=['Dubon2026.sourcePrimitive_exists_originalSupport_finiteResidualGalois_charP']
extra=['Dubon2026.sourcePrimitive_exists_originalSupport_oddResidualGalois_charP','Dubon2026.generalLinearSubalgebra_continuous','IntermediateField.finiteDimensional_adjoin','Module.finite_of_finite','RingHom.map_det','AddMonoidHom.map_trace']
required=list(dict.fromkeys(ths+defs+extra))
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=[])
def output(name,s):
 f=p/name;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-primitive-finite-residual-4-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda ns:'#['+', '.join(chr(96)+n for n in ns)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
template=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=template[template.index('private def runPlanarPairingAudit'):template.index('#lint in')]
for key,ns in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+key+r' : Array Name := #\[[^\n]*','let '+key+' : Array Name := '+arr(ns),body)
body=body.replace('SOURCE ORIGINAL PRIMITIVE TATE RESTRICTION','SOURCE PRIMITIVE FINITE RESIDUAL')
output('SourcePrimitiveFiniteResidualAudit4.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
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
dep=dep[:dep.index('  logInfo m!')]+ '  logInfo m!"SOURCE PRIMITIVE FINITE RESIDUAL DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the actual original all-weight prescribed-prime finite-field residual consumer. Only declaration values are traversed. Compactness and discreteness give finite matrix image; adjoining its entries over the actual finite residue field gives a finite coefficient field by native finite-dimensionality. The exact original matrices and continuity descend through the literal inclusion. The global cyclotomic determinant, actual complex-conjugation determinant, original Fourier traces, prime determinants and good-prime inertia are retained over that same finite field. Finiteness and coefficient descent are derived, not assumed. All-weight adic realization, local/image properties, automorphy and literal higher symmetric-power continuation remain open. 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourcePrimitiveFiniteResidualDependencyAudit4.lean',imports+dep)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
files=[prod/'CoefficientSubalgebraRepresentationContinuity.lean',prod/'ArithmeticFramedUniversalRing.lean',prod/'ArithmeticFixedDeterminantUniversality.lean',p/'SourcePrimitiveResidualOddness.lean']
math=Path(r'E:\Lean\Riemann Zeta\.lake\packages\mathlib\Mathlib')
files += [math/m for m in ['FieldTheory/IntermediateField/Adjoin/Basic.lean','RingTheory/Finiteness/Cardinality.lean','LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean','LinearAlgebra/Matrix/Trace.lean','Data/ZMod/Basic.lean']]
rd=dict(scope=575,chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> actual residual deformation input over a finite coefficient field -> descend the same original all-weight residual matrices and exact local/global identities',reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in files],shorterRoute='Reuse compact image in a discrete target, native finite-dimensionality of an algebraic finite adjoin, Module.finite_of_finite, exact general-linear coefficient mapping and the existing subalgebra-continuity reflection. Ring-hom uniqueness from ZMod gives cyclotomic coefficient naturality. Native determinant and trace mapping preserve every original source formula. This supplies the finite residual coefficient field required by ArithmeticFramedUniversalRing and ArithmeticFixedDeterminantUniversality without new coefficient or topology infrastructure.',assumptionsToDischarge='The original primitive form, weight at least two and prescribed prime supply an actual finite coefficient field of that characteristic and continuous original-support representation. Its global determinant is the original cyclotomic power k-1, its determinant at genuine complex conjugation is minus one, its Frobenius traces are the original coefficient reductions, and its good-prime inertia is trivial. Finiteness, coefficient-field descent and compatibility are derived.',remaining='All-weight adic realization and required local, image and regularity properties, arithmetic automorphy and literal higher symmetric-power continuation remain required. The finite-field result is an input to deformation theory, not an automorphy or analytic conclusion. 16/20; DUB-17--20 OPEN.',scratchImportClosure=localClosure,separatelyAxiomChecked=[])
output('primitive-finite-residual-route-575.json',json.dumps(rd,indent=2)+'\n')
print(json.dumps(dict(modules=len(mods),queries=len(cfg['queries']),theorems=len(ths),constructions=len(defs),edges=len(required))))
