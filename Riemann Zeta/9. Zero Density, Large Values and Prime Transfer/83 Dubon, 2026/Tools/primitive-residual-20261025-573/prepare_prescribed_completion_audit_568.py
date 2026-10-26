from pathlib import Path
import json,re,hashlib
p=Path(__file__).parent
prod=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
mods=['SourcePrescribedReductionPrime', 'SourceAdicCoefficientResidueComparison', 'SourcePrescribedCompletionResidue', 'SourceReductionCompletionBasePrime', 'SourceReductionCompletionPadicMap', 'SourceReductionCompletionFinite', 'SourcePadicCompletionValuation', 'SourceReductionCompletionLocalStructures', 'SourceOriginalPrescribedReductionResidual', 'SourceOriginalExactReductionResidual', 'SourceOriginalAlgebraicIntegerResidual']
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 s=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',f.read_text(encoding='utf-8'),flags=re.S))
 ns=re.search(r'^namespace (\S+)',s,re.M)[1]
 ths += [ns+'.'+n for n in re.findall(r"^theorem ([\w.']+)",s,re.M)]
 defs += [ns+'.'+n for n in re.findall(r"^(?:noncomputable\s+)?(?:def|abbrev) ([\w.']+)",s,re.M)]
roots=['Dubon2026.SourceFunctionField.OriginalChart.originalPrimitive_algebraicInteger_reduction_residual_realization']
extra=['Dubon2026.SourceFunctionField.OriginalChart.originalPrimitive_prescribed_residual_frobenius_realization','Dubon2026.SourceFunctionField.OriginalChart.originalPrimitive_prescribed_continuous_galois_realization','Dubon2026.sourcePrimitiveCoefficientField_numberField','Dubon2026.sourcePrimitiveFieldCoefficient_isIntegral','Dubon2026.originalRingOfIntegersQuotientEquivAdicResidueField','Dubon2026.originalAdicIntegerNormEquiv','Dubon2026.originalAdicBaseChangeMap_mem_integers','Dubon2026.originalAdic_isNonarchimedeanLocalField','Dubon2026.stableLattice_integral_residual_realization','Padic.adicCompletionEquiv','PadicInt.coe_adicCompletionIntegersEquiv_symm_apply','PadicInt.coe_adicCompletionIntegersEquiv_apply','Valuation.HasExtension.ofComapInteger','Matrix.charpoly_map']
separatelyChecked=['Dubon2026.sourceReductionPrime_below','Dubon2026.sourcePrescribedCompletionResidueMap_injective','Dubon2026.sourceReductionCompletionPadicMap_rational','Dubon2026.sourceAdicCoefficientResidueEquiv_mk']
required=list(dict.fromkeys([n for n in ths+defs if n not in separatelyChecked]+extra))
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=separatelyChecked)
def output(name,s):
 f=p/name;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-original-prescribed-completion-11-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda ns:'#['+', '.join('`'+n for n in ns)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
template=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=template[template.index('private def runPlanarPairingAudit'):template.index('#lint in')]
for key,ns in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+key+r' : Array Name := #\[[^\n]*','let '+key+' : Array Name := '+arr(ns),body)
body=body.replace('Primitive Tate Restriction','Prescribed Completion').replace('PRIMITIVE TATE RESTRICTION','PRESCRIBED COMPLETION')
output('SourceOriginalPrescribedCompletionAudit11.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
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
dep=dep[:dep.index('  logInfo m!')]+'  logInfo m!"SOURCE ORIGINAL PRESCRIBED COMPLETION DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the actual original primitive prescribed algebraic-integer residual consumer. Only declaration values are traversed. The reduction kernel selects the genuine coefficient-field prime. The native rational completion equivalence and proved completed field embedding supply the finite Tate-prime extension and module topology. Their actual integer rings prove valuation compatibility. The proved quotient/residue equivalence constructs the residue embedding agreeing with the prescribed reduction on every integer. The existing prescribed Tate/lattice consumer then supplies the finite-image continuous representation, exact Frobenius polynomial, trace, determinant and good-prime inertia identity. Number-field, local coefficient, valuation, embedding, stable lattice and reduction compatibility inputs are discharged from the original primitive form and prescribed map. Four separate public auxiliary or definitional laws remain explicitly and exhaustively checked, without a claim of named use in this terminal proof. Arithmetic quotient and norm-local comparisons, closure of the parabolic branch, weight twist and support comparison, automorphy and all-weight continuation remain required. 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceOriginalPrescribedCompletionDependencyAudit11.lean',imports+dep)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
mathlib=Path(r'E:\Lean\Riemann Zeta\.lake\packages\mathlib\Mathlib')
files=[prod/(m+'.lean') for m in ['OriginalAdicBaseChangeMap','OriginalAdicCompletionResidue','OriginalAdicIntegerNormComparison','OriginalAdicLocalFieldStructures','OriginalIntegerLocalValuationMap','OriginalFinitePrimeOrbits','SourcePrimitiveLocalCoefficients','SourcePrimitiveAlgebraicIntegerReduction','SourcePrimitiveGaloisAlternative','RationalArithmeticGaloisGroup']]+[mathlib/m for m in ['NumberTheory/NumberField/Completion/FinitePlace.lean','NumberTheory/Padics/HeightOneSpectrum.lean','Topology/Algebra/Module/FiniteDimension.lean','RingTheory/Valuation/Extension.lean','Algebra/Algebra/Hom/Rat.lean']]
rd=dict(scope=568,chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> all-weight residual association -> close the weight-two parabolic branch -> actual original primitive residual representation with the prescribed complex algebraic-integer reduction -> choose the Fourier-field completion at the reduction kernel and prove its actual residue embedding and Tate-prime compatibility',reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in files],shorterRoute='Use the kernel of the prescribed reduction as the actual Fourier-integer prime. Reuse the existing completion quotient/residue equivalence, rather than a new algebraic-closure embedding or valuation extension construction. Compose the native rational p-adic completion equivalence with the existing completed number-field embedding. Native finiteness of completed number fields, continuous scalar multiplication and finite-dimensional module topology supply the exact local structure. The native integer-ring equivalence proves valuation compatibility without an isometry between differently normalized adic norms. A number-field-parametric assembly keeps elaboration bounded; instantiate it with the actual proved Fourier number field and identity embedding, then restrict the exact complex algebraic-integer reduction. Finite image is retained for the necessary next arithmetic-quotient descent. No proof limits change.',assumptionsToDischarge='The completion, its Tate-prime scalar map, finite-dimensional module topology, nonarchimedean local-field structure and valuation extension are constructed. Its actual residue embedding agrees with the prescribed reduction on every original integer. The actual original Tate/lattice construction therefore gives a finite-image continuous residual representation with the prescribed reduced original coefficient, Frobenius polynomial, trace, determinant and good-prime inertia, without supplying any coefficient completion, embedding, local structure, lattice or compatibility assumption.',remaining='Arithmetic quotient and norm-local interface comparisons, closure of the weight-two parabolic branch, final weight twist and support comparison, arithmetic automorphy and all-weight continuation remain required. 16/20; DUB-17--20 OPEN.',scratchImportClosure=localClosure,separatelyAxiomChecked=separatelyChecked)
output('prescribed-completion-route-568.json',json.dumps(rd,indent=2)+'\n')
print(json.dumps(dict(modules=len(mods),queries=len(cfg['queries']),theorems=len(ths),constructions=len(defs),edges=len(required))))
