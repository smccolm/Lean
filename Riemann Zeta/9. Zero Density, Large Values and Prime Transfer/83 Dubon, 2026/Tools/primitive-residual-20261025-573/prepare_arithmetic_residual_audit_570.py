from pathlib import Path
import json,re,hashlib
p=Path(__file__).parent
prod=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
mods=['SourceValuationResidualAction', 'SourceNormValuationRestriction', 'SourceRationalLocalValuation', 'SourceOriginalNormLocalResidual', 'SourceNumberFieldNormInertiaLift', 'SourceAbsoluteFiniteUnramified', 'SourceNumberFieldSupportRamification', 'SourceAbsoluteArithmeticRestriction', 'SourceAbsoluteArithmeticDescent', 'SourceArithmeticLocalEmbeddingExtension', 'SourceOriginalArithmeticResidual']
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 s=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',f.read_text(encoding='utf-8'),flags=re.S))
 ns=re.search(r'^namespace (\S+)',s,re.M)[1]
 ths += [ns+'.'+n for n in re.findall(r"^theorem ([\w.']+)",s,re.M)]
 defs += [ns+'.'+n for n in re.findall(r"^(?:noncomputable\s+)?(?:def|abbrev) ([\w.']+)",s,re.M)]
roots=['Dubon2026.SourceFunctionField.OriginalChart.originalPrimitive_prescribed_arithmetic_residual_realization']
extra=['Dubon2026.SourceFunctionField.OriginalChart.originalPrimitive_algebraicInteger_reduction_residual_realization', 'Dubon2026.continuous_galois_faithful_finite_factor', 'Dubon2026.originalGeneratedLocalField_exists_closure_inertia_lift', 'Dubon2026.embeddedFiniteGaloisCompositum', 'Dubon2026.embeddedFiniteGaloisCompositum_ranges', 'Dubon2026.numberField_unramifiedIn_of_inertia_eq_bot', 'Dubon2026.originalIntegerPrimeBelow_exists_prime', 'Dubon2026.originalSupport_exists_embedding', 'Dubon2026.embeddedNormalGaloisRestriction_continuous', 'Dubon2026.rationalPrimeArithmeticRestriction_commutes', 'Dubon2026.completeNonarchimedeanGalois_norm_map', 'IsAlgClosed.lift']
separatelyChecked=[]
required=list(dict.fromkeys([n for n in ths+defs if n not in separatelyChecked]+extra))
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=separatelyChecked)
def output(name,s):
 f=p/name;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-original-arithmetic-residual-11-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda ns:'#['+', '.join('`'+n for n in ns)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
template=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=template[template.index('private def runPlanarPairingAudit'):template.index('#lint in')]
for key,ns in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+key+r' : Array Name := #\[[^\n]*','let '+key+' : Array Name := '+arr(ns),body)
body=body.replace('Primitive Tate Restriction','Arithmetic Residual').replace('PRIMITIVE TATE RESTRICTION','ARITHMETIC RESIDUAL')
output('SourceOriginalArithmeticResidualAudit11.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
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
dep=dep[:dep.index('  logInfo m!')]+'  logInfo m!"SOURCE ORIGINAL ARITHMETIC RESIDUAL DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the actual original primitive prescribed arithmetic residual consumer. Only declaration values are traversed. The original prescribed reduction gives one finite-image absolute representation. Literal norm-valuation restriction supplies its original inertia and Frobenius actions through every embedding. The existing generated-compositum inertia lift makes its faithful finite factor unramified outside the support. The proved original-support embedding and continuous restriction construct its arithmetic descent. The already chosen arithmetic local embedding extends to the absolute closure, and the actual restrictions commute. The same arithmetic representation retains finite image, the exact characteristic polynomial, trace, determinant and inertia identities. No local comparison, field ramification, support containment, arithmetic descent or chosen-embedding agreement is assumed. Closing the parabolic branch, final weight twist and support comparison, automorphy and all-weight continuation remain required. 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceOriginalArithmeticResidualDependencyAudit11.lean',imports+dep)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
files=[prod/(m+'.lean') for m in ['OriginalGeneratedLocalInertiaLift','EmbeddedFiniteGaloisCompositumMaps','ContinuousGaloisFaithfulFiniteFactor','NumberFieldUnramifiedOfTrivialInertia','OriginalIntegerPrimeTower','OriginalSupportRamificationTransport','EmbeddedNormalGaloisRestrictionContinuity','RationalPrimeArithmeticRestriction','SourcePrimitiveGaloisAlternative','SourceParabolicCuspEigenlift','SourceWeightTwoFullEigenlift']]
rd=dict(scope=570,chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> all-weight residual association -> close the weight-two parabolic branch -> original primitive prescribed reduction -> actual norm-local action and arithmetic quotient',reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in files],shorterRoute='Reuse the existing generated finite local compositum and inertia lift, faithful finite factor, original prime classification, support embedding, and continuous embedded restriction. Derive finite-field unramifiedness from actual inertia and faithfulness. Extend the already chosen arithmetic local embedding using the native algebraically closed-field lift, then prove equality of the actual restriction maps. Equality of the unique rational algebra structures handles presentation differences without changing the embedding. No new valuation-extension, Galois-union, or local-field theory is constructed.',assumptionsToDischarge='Norm-local compatibility, finite-field ramification, original-support containment, continuous arithmetic descent, and agreement with the fixed arithmetic local maps are all derived for the original prescribed-reduction representation. The terminal theorem keeps the same finite-image representation and exact good-prime characteristic polynomial, trace, determinant and inertia identities.',remaining='The parabolic cusp eigensystem still needs a primitive lower-level realization and the resulting arithmetic consumer. Final weight twist and support comparison, arithmetic automorphy and all-weight continuation remain required. 16/20; DUB-17--20 OPEN.',scratchImportClosure=localClosure,separatelyAxiomChecked=separatelyChecked)
output('arithmetic-residual-route-570.json',json.dumps(rd,indent=2)+'\n')
print(json.dumps(dict(modules=len(mods),queries=len(cfg['queries']),theorems=len(ths),constructions=len(defs),edges=len(required))))
