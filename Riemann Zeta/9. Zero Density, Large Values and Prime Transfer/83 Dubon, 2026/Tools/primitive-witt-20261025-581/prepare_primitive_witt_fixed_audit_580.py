from pathlib import Path
import json,re,hashlib
p=Path(__file__).parent
prod=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
mods=['SourcePadicWittCoefficient','SourceArithmeticPadicCyclotomic','SourceArithmeticPadicCyclotomicReduction','SourceArithmeticWittCyclotomic','SourceResidualWittFixedDeterminant','SourceResidualWittFixedRing','SourcePrimitiveWittFixedResidual']
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean')
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 s=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',f.read_text(encoding='utf-8'),flags=re.S))
 ns=re.search(r'^namespace (\S+)',s,re.M)[1]
 ths += [ns+'.'+n for n in re.findall(r"^theorem ([\w.']+)",s,re.M)]
 defs += [ns+'.'+n for n in re.findall(r"^(?:noncomputable\s+)?(?:def|abbrev) ([\w.']+)",s,re.M)]
roots=['Dubon2026.sourcePrimitive_exists_originalSupport_wittFixedResidualGalois_charP']
extra=['Dubon2026.sourcePrimitive_exists_originalSupport_wittFramedResidualGalois_charP','Dubon2026.arithmeticFixedDeterminantRing_localData','Dubon2026.arithmeticFixedDeterminantRepresentation_residue','Dubon2026.arithmeticFixedDeterminantRepresentation_det','Dubon2026.sourceUnramifiedUnion_mono_dvd_pow','Dubon2026.originalQUnramifiedUnion_exists_primitiveRoot','WittVector.fromPadicInt','cyclotomicCharacter.spec','cyclotomicCharacter.continuous']
separate=['Dubon2026.sourcePadicWittCoefficient_injective']
required=list(dict.fromkeys([n for n in ths+defs if n not in separate]+extra))
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=separate)
def output(name,s):
 f=p/name;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-primitive-witt-fixed-7-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda ns:'#['+', '.join(chr(96)+n for n in ns)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
template=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=template[template.index('private def runPlanarPairingAudit'):template.index('#lint in')]
for key,ns in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+key+r' : Array Name := #\[[^\n]*','let '+key+' : Array Name := '+arr(ns),body)
body=body.replace('SOURCE ORIGINAL PRIMITIVE TATE RESTRICTION','SOURCE PRIMITIVE WITT FIXED')
output('SourcePrimitiveWittFixedAudit7.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
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
dep=dep[:dep.index('  logInfo m!')]+ '  logInfo m!"SOURCE PRIMITIVE WITT FIXED DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the actual original all-weight fixed-determinant residual consumer. Only declaration values are traversed. Every prime-power root lies in the same original arithmetic extension by proved support-power inclusion. The native continuous p-adic cyclotomic character therefore has the actual root action and reduces to the original finite character. Its native Witt scalar image has exactly the required residual determinant. The actual fixed-determinant quotient is Noetherian and complete; its universal matrices reduce to the same original residual representation and have the genuine cyclotomic weight power as determinant. The original source Fourier traces, real determinant and good-prime inertia are retained. Scalar-map injectivity is separately axiom-checked. No characteristic-zero point or original all-weight adic association is asserted. Local/image/regularity properties, arithmetic automorphy and literal higher symmetric-power continuation remain open. 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourcePrimitiveWittFixedDependencyAudit7.lean',imports+dep)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
files=[prod/'SourceArithmeticSupportPowers.lean',prod/'UnramifiedUnionCyclotomicRoots.lean',prod/'RationalArithmeticCyclotomicCharacter.lean',prod/'ArithmeticFixedDeterminantRepresentation.lean',prod/'ArithmeticFixedDeterminantRing.lean',prod/'ArithmeticFixedDeterminantUniversality.lean',p/'SourcePrimitiveWittFramedResidual.lean',p/'SourceResidualWittCoefficients.lean']
math=Path(r'E:\\Lean\\Riemann Zeta\\.lake\\packages\\mathlib\\Mathlib')
files += [math/m for m in ['RingTheory/WittVector/Compare.lean','NumberTheory/Cyclotomic/CyclotomicCharacter.lean','NumberTheory/Padics/RingHoms.lean']]
rd=dict(scope=580,chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> actual residual fixed-determinant deformation problem -> construct the genuine p-adic cyclotomic weight character, prove its exact reduction and consume it in the existing actual quotient',reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in files],shorterRoute='Native WittVector.fromPadicInt and cyclotomicCharacter supply the original mixed-characteristic scalar and character. Existing support-power monotonicity supplies every prime-power root in the same arithmetic extension; original primitive-root action identifies reduction. Reuse the existing fixed-determinant quotient, local-ring proof and universal representation; do not rebuild deformation representability or general p-adic coefficient-lift infrastructure.',assumptionsToDischarge='For the original all-weight primitive form, supply the actual p-adic cyclotomic weight determinant over Witt coefficients, prove its exact residual compatibility, and construct the resulting Noetherian complete fixed-determinant quotient with exact original residual matrices and universal determinant. Preserve every original Fourier, real and good-prime inertia clause.',remaining='No characteristic-zero specialization of this quotient is supplied. Original all-weight adic association, required local/image/regularity properties, arithmetic automorphy and literal higher symmetric-power continuation remain required. 16/20; DUB-17--20 OPEN.',scratchImportClosure=localClosure,separatelyAxiomChecked=separate,renewedExternalReview='reuse-20261025-579/reuse-assessment.json')
output('primitive-witt-fixed-route-580.json',json.dumps(rd,indent=2)+'\n')
print(json.dumps(dict(modules=len(mods),queries=len(cfg['queries']),theorems=len(ths),constructions=len(defs),edges=len(required))))
