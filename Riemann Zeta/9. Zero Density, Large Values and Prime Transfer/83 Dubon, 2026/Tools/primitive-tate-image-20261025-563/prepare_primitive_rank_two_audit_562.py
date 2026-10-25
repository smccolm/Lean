from pathlib import Path
import json,re,hashlib
p=Path(__file__).parent
prod=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
mods=['SourceCharacterIdempotentLine','SourceCharacterIdempotentRankTwo','SourceGeneratedCharacterIdempotent','SourceTensorCharacterIdempotent','SourceOriginalCuspPadicHeckeMap','SourceIntegerCoefficientExtensionCharacter','SourcePrimitiveHeckeAlgebraEvaluation','SourcePrimitiveHeckeAlgebraProjector','SourceRankTwoSurjectiveDescent','SourceOriginalCuspTateRankTwo','SourceRankTwoBaseChange','SourceIntegerCoefficientRankTwo','SourceIntertwinedRangeEquiv','SourceRankTwoCharacterRange','SourcePrimitiveHeckeAlgebraRankTwo','SourcePrimitiveOriginalTateRankTwo','SourcePrimitiveOriginalTateNondegenerateRankTwo']
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 s=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',f.read_text(encoding='utf-8'),flags=re.S))
 ns=re.search(r'^namespace (\S+)',s,re.M)[1]
 ths += [ns+'.'+n for n in re.findall(r"^theorem ([\w.']+)",s,re.M)]
 defs += [ns+'.'+n for n in re.findall(r"^(?:noncomputable\s+)?(?:def|abbrev) ([\w.']+)",s,re.M)]
sf='Dubon2026.SourceFunctionField.OriginalChart.'
roots=[sf+'exists_primitive_originalTate_nondegenerate_rankTwo','Dubon2026.rankTwoCharacterRangeEquiv_apply']
extra=[sf+n for n in ['originalRationalTate_explicit_word_rankTwo','originalLatticeCuspHeckeEquiv_word','originalPadicHeckeEigencharacter_integral','primitiveOriginalTateEvaluation_projector_selfAdjoint']]+['Dubon2026.'+n for n in ['sourceIntegralCuspHeckeWord_surjective','SourceHeckeMatrixDescent.explicit_descent_prime_generators','sourcePrimitiveFieldHeckeCharacter_hecke','exists_primitive_tensor_projection','primitiveTensorEigencharacter_projector','SourceFunctionField.originalCoefficientWeilBilinear_injective','mapped_idempotent_pairing_restriction','algebraIdempotentLeftIdeal']]+['LinearEquiv.baseChange','TensorProduct.piRight','LinearEquiv.ofSubmodules','Algebra.adjoin_induction','AlgHom.liftEquiv','LinearEquiv.piCongrRight','LinearEquiv.ofInjective','LinearMap.range_compLeft','LinearEquiv.ofEq']
required=list(dict.fromkeys(ths+extra))
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots)
def output(name,s):
 f=p/name;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-original-primitive-rank-two-17-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda ns:'#['+', '.join('`'+n for n in ns)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
template=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=template[template.index('private def runPlanarPairingAudit'):template.index('#lint in')]
for key,ns in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+key+r' : Array Name := #\[[^\n]*','let '+key+' : Array Name := '+arr(ns),body)
body=body.replace('Primitive Tate Restriction','Primitive Rank Two').replace('PRIMITIVE TATE RESTRICTION','PRIMITIVE RANK TWO')
output('SourceOriginalPrimitiveRankTwoAudit17.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
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
dep=dep[:dep.index('  logInfo m!')]+"  logInfo m!\"SOURCE ORIGINAL PRIMITIVE RANK TWO DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the actual original nondegenerate rank-two Tate image consumer or its exact prescribed-character coordinate law. Only declaration values are traversed. Existing integral word coordinates descend through the same cusp Hecke presentation and extend by native tensor/product equivalences. The original p-adic Hecke character retains every integral eigenvalue, and the arithmetic projector has character one and scalar character action. Its actual Tate image is rank two, and the same projector has an injective restricted root-valued Weil pairing. No image-dimension, nonzero-image, comparison, generator, character-compatibility or restricted-injectivity assumption is supplied. Comparison to the existing spanning primitive specialization, primitive Frobenius determinant and remaining DUB-17--20 conclusions stay open; 16/20.\"\n\n#eval runPlanarPairingDependencyAudit\n"
output('SourceOriginalPrimitiveRankTwoDependencyAudit17.lean',imports+dep)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
mathlib=Path(r'E:\Lean\Riemann Zeta\.lake\packages\mathlib\Mathlib')
files=[prod/(m+'.lean') for m in ['AlgebraIdempotentLeftIdeal','SourceExplicitRankTwoCoordinates','SourceOriginalExplicitHeckeRankTwo','SourceOriginalPadicEigencharacter','SourceOriginalPrimitiveTateSpecialization','SourceOriginalPrimitiveFrobeniusQuadraticRealization','SourceGeneratedHeckeLinearity','EigenlineCharacter','SourceMatrixAlgebraSpecialization','SourceRankTwoCoefficientSpecialization']]+[p/(m+'.lean') for m in ['SourcePrimitiveOriginalTateRestriction','SourcePrimitiveOriginalTateEvaluation','SourcePrimitiveTensorProjection','SourceOriginalCuspRationalTateHecke']]+[mathlib/s for s in ['LinearAlgebra/TensorProduct/Pi.lean','LinearAlgebra/TensorProduct/Tower.lean','Algebra/Module/Submodule/Equiv.lean']]
rd=dict(scope=562,chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> residual association -> primitive Frobenius determinant -> nonzero required primitive component pairing -> actual nondegenerate rank-two arithmetic-projector Tate image',reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in files],shorterRoute='Reuse the all-word original rank-two theorem and the surjective integral cusp presentation; no second determinant descent or free rank proof is needed. Native finite-product tensor base change retains literal coordinates. The already proved original p-adic eigencharacter supplies compatibility on every integral operator, and existing prime generation extends scalar action. The existing algebraIdempotentLeftIdeal and native range/submodule equivalences identify the normalized character image with the prescribed two coefficient coordinates. The same arithmetic projector is used for rank two and restricted Weil nondegeneracy. A direct large-expression rewrite was replaced by a finite-algebra surjective-descent lemma at unchanged proof limits. The alternative full tensor-associativity reconstruction and a new eigencharacter construction were assessed and deferred because the existing character and all-word coordinates suffice.',assumptionsToDischarge='The transported arithmetic projector has a nonzero rank-two image on the actual original coefficient-extended Tate module, and its literal root-valued Weil pairing is injective on that same image. Generator, integral-character compatibility, action comparison and dimension hypotheses are all derived from the original upstream objects.',remaining='The image coordinate equivalence still needs comparison with the existing spanning primitive specialization. The cyclotomic law must yield the separate primitive Frobenius determinant; the quadratic identity alone is insufficient. Residual association, arithmetic automorphy and all-weight continuation remain required. 16/20; DUB-17--20 OPEN.',scratchImportClosure=localClosure)
output('primitive-rank-two-route-562.json',json.dumps(rd,indent=2)+'\n')
print(json.dumps(dict(modules=len(mods),queries=len(cfg['queries']),theorems=len(ths),constructions=len(defs),edges=len(required))))
