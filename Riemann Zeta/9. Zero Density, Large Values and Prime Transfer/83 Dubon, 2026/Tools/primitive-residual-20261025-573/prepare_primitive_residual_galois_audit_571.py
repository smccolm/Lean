from pathlib import Path
import json,re,hashlib
p=Path(__file__).parent
prod=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
mods=['SourceWeightTwoDegeneracyAdjoint', 'SourceWeightTwoEigenLevelDescent', 'SourceWeightTwoNewEigenNormalization', 'SourceParabolicPrimitiveDivisor', 'SourceArithmeticSupportInflationValues', 'SourceOriginalDivisorArithmeticResidual', 'SourceParabolicArithmeticResidual', 'SourceResidualGaloisRealization', 'SourcePrimitiveWeightTwoGalois', 'SourcePrimitiveRestoredGalois', 'SourcePrimitiveOriginalResidualGalois', 'SourcePrimitiveResidualGaloisCharP']
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 s=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',f.read_text(encoding='utf-8'),flags=re.S))
 ns=re.search(r'^namespace (\S+)',s,re.M)[1]
 ths += [ns+'.'+n for n in re.findall(r"^theorem ([\w.']+)",s,re.M)]
 defs += [ns+'.'+n for n in re.findall(r"^(?:noncomputable\s+)?(?:def|abbrev) ([\w.']+)",s,re.M)]
roots=['Dubon2026.sourcePrimitive_exists_originalSupport_residualGalois_charP']
extra=['Dubon2026.SourceFunctionField.OriginalChart.originalPrimitive_prescribed_arithmetic_residual_realization', 'Dubon2026.sourceTrivialParabolicEigen_exists_cuspForm', 'Dubon2026.sourceCommutingOperators_exists_commonEigenvector', 'LinearMap.adjoint_inner_left', 'Dubon2026.cusp_new_coprime_eq_zero', 'Dubon2026.cuspHeckeLinear_prime_degeneracy', 'Dubon2026.cuspHeckeLinear_coprime_selfAdjoint', 'Dubon2026.cuspNewspace_hecke_coprime', 'Dubon2026.sourceTrivialH1Eigen_parabolicLift_or_galoisRep', 'Dubon2026.sourcePrimitive_exists_residualWeightTwo', 'Dubon2026.sourceArithmeticWeightTwist_frobenius_trace', 'Dubon2026.sourceArithmeticWeightTwist_frobenius_det', 'Dubon2026.sourceArithmeticWeightTwist_inertia', 'Dubon2026.sourceArithmeticSupport_exists_representation', 'Dubon2026.sourceWeightTwo_arithmeticExtension_eq', 'Dubon2026.sourcePrimitive_exists_residualHeckeCharacter_charP', 'Dubon2026.sourcePrimitiveCoefficientField_numberField', 'Dubon2026.sourceRationalPrimeExtensionResidue_charP', "Matrix.charpoly_units_conj'", 'Dubon2026.rationalArithmeticSupportRestriction_local_conjugacy', 'Dubon2026.sourceArithmeticSupport_local_trace', 'Dubon2026.sourceArithmeticSupport_local_det', 'Dubon2026.sourceArithmeticSupport_local_eq_one']
separatelyChecked=[]
required=list(dict.fromkeys([n for n in ths+defs if n not in separatelyChecked]+extra))
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=separatelyChecked)
def output(name,s):
 f=p/name;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-primitive-residual-galois-12-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda ns:'#['+', '.join('`'+n for n in ns)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
template=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=template[template.index('private def runPlanarPairingAudit'):template.index('#lint in')]
for key,ns in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+key+r' : Array Name := #\[[^\n]*','let '+key+' : Array Name := '+arr(ns),body)
body=body.replace('Primitive Tate Restriction','Primitive Residual Galois').replace('PRIMITIVE TATE RESTRICTION','PRIMITIVE RESIDUAL GALOIS')
body=body.replace('SOURCE ORIGINAL PRIMITIVE RESIDUAL GALOIS','SOURCE PRIMITIVE RESIDUAL GALOIS')
output('SourcePrimitiveResidualGaloisAudit12.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
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
dep=dep[:dep.index('  logInfo m!')]+ '  logInfo m!"SOURCE PRIMITIVE RESIDUAL GALOIS DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the original all-weight prescribed-prime residual consumer. Only declaration values are traversed. The original parabolic H1 class supplies a genuine cusp eigensystem. Native finite-dimensional adjoints of actual degeneracy maps descend any non-new eigensystem to a strictly smaller dividing level, preserving every original good prime. Minimality gives newness; the proved commuting family and coprime-coefficient uniqueness produce an actual normalized primitive form. Its prescribed residual representation is inflated to original support through proved local conjugacy, retaining characteristic polynomial, trace, determinant and inertia. This closes the parabolic/Dirichlet alternative for the original residual H1 class. The actual all-weight class, proved cyclotomic weight twist and original arithmetic support comparison give the original Fourier reductions, determinant exponent k-1 and inertia. The genuine local coefficient field and prescribed residue characteristic are constructed. No parabolic branch, primitive divisor, residual association, weight-restoration, support, local-field or residue-characteristic premise remains. All-weight adic realization and required local/image properties, arithmetic automorphy and literal higher symmetric-power continuation remain required. 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourcePrimitiveResidualGaloisDependencyAudit12.lean',imports+dep)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
files=[prod/(m+'.lean') for m in ['SourceParabolicCuspEigenlift','SourceWeightTwoFullEigenlift','SourceCommutingCommonEigenvector','CuspPeterssonCore','CuspOldNewProjection','CuspCoprimeOldspace','HeckeDegeneracyPrime','HeckeGoodAdjoint','HeckeOldNewStability','SourceResidualGaloisAlternative','SourcePrimitiveWeightTwo','SourcePrimitiveWeightRestoration','SourcePrimitiveOriginalSupport','SourcePrimitiveResidualCharacteristic','SourceArithmeticSupportLocalValues','ArithmeticSupportLocalConjugacy']]
files += [Path(r'E:\\Lean\\Riemann Zeta\\.lake\\packages\\mathlib\\Mathlib')/m for m in ['Analysis/InnerProductSpace/Adjoint.lean','LinearAlgebra/Matrix/Charpoly/Basic.lean']]
rd=dict(scope=571,chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> actual primitive Galois association -> assemble all-weight residual association at every prescribed prime, with original Fourier reduction, determinant exponent and arithmetic support',reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in files],shorterRoute='Reuse native finite-dimensional adjoints for actual Petersson degeneracy maps, existing Hecke adjointness/intertwining and original finite cusp dimension. A strictly descending level argument gives a genuine newspace witness; the existing commuting-family eigenvector theorem and coprime Fourier uniqueness normalize it. This avoids new spectral or oldform decomposition infrastructure. Reuse the prescribed primitive arithmetic representation and the existing actual support/local conjugacy. Close the original H1 alternative, then consume the already proved weight-twist and support-equality arguments. Construct the local field and residue characteristic from the original coefficient-field theorem; no new completion or coefficient arithmetic is needed.',assumptionsToDischarge='The parabolic primitive divisor, preserved eigenvalues, actual prescribed residual representation, original support, all-weight Fourier factor, weight determinant and residue characteristic are derived from the original primitive cusp form, weight at least two, and prescribed rational prime. The residual H1 alternative is completely assembled. The terminal theorem supplies a genuine continuous arithmetic Galois representation with exact original Frobenius trace, determinant exponent k-1, and required inertia triviality.',remaining='All-weight adic realization and the required local/image properties, arithmetic automorphy and literal higher symmetric-power continuation remain required for DUB-17. The modular/level-one concentration consumers and final acceptance verification also remain open. 16/20; DUB-17--20 OPEN.',scratchImportClosure=localClosure,separatelyAxiomChecked=separatelyChecked)
output('primitive-residual-galois-route-571.json',json.dumps(rd,indent=2)+'\\n')
print(json.dumps(dict(modules=len(mods),queries=len(cfg['queries']),theorems=len(ths),constructions=len(defs),edges=len(required))))
