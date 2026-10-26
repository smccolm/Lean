from pathlib import Path
import json,re,hashlib
p=Path(__file__).parent
prod=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
mods=['SourceSpanningProjectorImage', 'SourceSpecializationBaseChangeIntertwiner', 'SourcePolynomialSpecialization', 'SourceOriginalSpecializationProjector', 'SourceOriginalSpecializationPrimitiveImage', 'SourcePolynomialCommutant', 'SourcePrimitiveOriginalTateGalois', 'SourceImageSpecializationPairing', 'SourceAlternatingRankTwoDeterminant', 'SourceImageSpecializationDeterminant', 'SourceOriginalSpecializationCyclotomicDeterminant', 'SourceOriginalPrimitiveCyclotomicRealization']
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 s=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',f.read_text(encoding='utf-8'),flags=re.S))
 ns=re.search(r'^namespace (\S+)',s,re.M)[1]
 ths += [ns+'.'+n for n in re.findall(r"^theorem ([\w.']+)",s,re.M)]
 defs += [ns+'.'+n for n in re.findall(r"^(?:noncomputable\s+)?(?:def|abbrev) ([\w.']+)",s,re.M)]
roots=['Dubon2026.SourceFunctionField.OriginalChart.originalPrimitive_continuous_unramified_cyclotomic_realization']
extra=['Dubon2026.SourceFunctionField.OriginalChart.exists_primitive_originalTate_nondegenerate_rankTwo', 'Dubon2026.SourceFunctionField.OriginalChart.originalRationalTateGaloisRep_prime_commute', 'Dubon2026.SourceFunctionField.OriginalChart.originalPrimitive_continuous_unramified_frobenius_quadratic_realization', 'Dubon2026.SourceFunctionField.OriginalChart.originalPeriodLatticeBasis', 'Dubon2026.SourceFunctionField.originalCoefficientWeilBilinear_self', 'Dubon2026.SourceFunctionField.originalCoefficientWeilBilinear_cyclotomic', 'Dubon2026.SourceFunctionField.finite_original_regularDifferentials', 'Dubon2026.SourceFunctionField.nonempty_original_places', 'LinearMap.range_liftBaseChange', 'LinearMap.injective_iff_surjective_of_finrank_eq_finrank', 'Module.Finite.of_injective', 'LinearEquiv.ofBijective', 'Polynomial.smeval_commute_left', 'Commute.sum_right', 'Module.End.baseChangeHom']
required=list(dict.fromkeys(ths+extra))
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots)
def output(name,s):
 f=p/name;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-original-primitive-cyclotomic-12-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda ns:'#['+', '.join('`'+n for n in ns)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
template=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=template[template.index('private def runPlanarPairingAudit'):template.index('#lint in')]
for key,ns in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+key+r' : Array Name := #\[[^\n]*','let '+key+' : Array Name := '+arr(ns),body)
body=body.replace('Primitive Tate Restriction','Primitive Cyclotomic').replace('PRIMITIVE TATE RESTRICTION','PRIMITIVE CYCLOTOMIC')
output('SourceOriginalPrimitiveCyclotomicAudit12.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
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
dep=dep[:dep.index('  logInfo m!')]+'  logInfo m!"SOURCE ORIGINAL PRIMITIVE CYCLOTOMIC DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the same actual primitive representation consumer. Only declaration values are traversed. Native scalar-extension range gives surjectivity of the existing spanning specialization. Its original Hecke eigenvalues prove that it fixes the actual arithmetic projector, so its restriction to the nondegenerate rank-two image is an isomorphism. Original Hecke-Galois commutation preserves that image. The literal Weil pairing transports through this same specialization, and its nonzero alternating rank-two value detects the determinant as the original cyclotomic multiplier. The final consumer retains the same actual continuous unramified representation, all prime eigenvalues and the Frobenius quadratic identity without pairing, projector, image, determinant or comparison hypotheses. The cyclotomic value at the source Frobenius lifts, the resulting trace and characteristic polynomial, residual association and remaining DUB-17--20 conclusions remain open; 16/20."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceOriginalPrimitiveCyclotomicDependencyAudit12.lean',imports+dep)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
mathlib=Path(r'E:\Lean\Riemann Zeta\.lake\packages\mathlib\Mathlib')
files=[prod/(m+'.lean') for m in ['SourcePrimitiveOriginalTateNondegenerateRankTwo', 'SourceOriginalCoefficientWeilLaws', 'SourceOriginalRationalTateGalois', 'SourceOriginalPrimitiveFrobeniusQuadraticRealization', 'SourceOriginalPrimitiveGaloisRealization', 'PolynomialEndIntertwiner', 'SourcePolynomialKernelProjectionLaws', 'SourceOriginalCyclotomicLocal', 'SourceLocalCyclotomicAction', 'SourceHeckePrimeRootReduction']]+[mathlib/s for s in ['RingTheory/TensorProduct/Basic.lean','LinearAlgebra/FiniteDimensional/Lemmas.lean','Algebra/Polynomial/Smeval.lean','LinearAlgebra/SesquilinearForm/Basic.lean','LinearAlgebra/Determinant.lean']]
rd=dict(scope=564,chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> residual association -> primitive Frobenius determinant -> determinant of the existing actual primitive representation equals the original cyclotomic character -> specialization identifies the nondegenerate invariant rank-two Tate image',reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in files],shorterRoute='Reuse native range_liftBaseChange and equal-finite-dimension bijectivity to keep the existing spanning specialization itself. Its prime eigenvalues annihilate the finite good-prime squared shifts; adapt the existing complex polynomial-intertwiner proof only to the necessary zero-action case over the coefficient field. Original prime Hecke-Galois commutation and native finite-sum/polynomial commutation make the same image invariant. Transfer the literal vector-valued Weil pairing through that exact specialization. The native scalar-valued alternating-map determinant theorem does not cover its original target; the direct two-coordinate bilinear expansion proves precisely the needed vector-valued determinant identity without a target basis or a new polarization. The final consumer unpacks the already constructed continuous unramified representation and retains its original Frobenius quadratic identity. Existing local root separation and cyclotomic Frobenius results were inspected for the next exact valuation-subring Frobenius bridge; they are not yet claimed as consumed or proved for that source interface.',assumptionsToDischarge='The actual existing spanning primitive specialization restricts to an isomorphism on the same nondegenerate rank-two projector image. The original Galois action preserves that image. Its transported literal Weil pairing is nondegenerate and alternating with the original cyclotomic multiplier. Therefore the same already constructed primitive representation has exactly that determinant, with no pairing, projector, image, invariance or determinant assumption supplied.',remaining='The cyclotomic multiplier must be evaluated at the exact source arithmetic Frobenius lifts to give the rational prime, and combined with the retained quadratic identity to obtain trace and characteristic polynomial. Residual association, arithmetic automorphy and all-weight continuation remain required. 16/20; DUB-17--20 OPEN.',scratchImportClosure=localClosure)
output('primitive-cyclotomic-route-564.json',json.dumps(rd,indent=2)+'\n')
print(json.dumps(dict(modules=len(mods),queries=len(cfg['queries']),theorems=len(ths),constructions=len(defs),edges=len(required))))
