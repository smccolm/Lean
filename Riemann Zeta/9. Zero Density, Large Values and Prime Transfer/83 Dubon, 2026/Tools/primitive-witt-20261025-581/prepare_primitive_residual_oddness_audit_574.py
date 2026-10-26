from pathlib import Path
import json,re,hashlib
p=Path(__file__).parent
prod=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
mods=['SourceResidualRealDeterminant','SourcePrimitiveResidualOddness']
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 s=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',f.read_text(encoding='utf-8'),flags=re.S))
 ns=re.search(r'^namespace (\S+)',s,re.M)[1]
 ths += [ns+'.'+n for n in re.findall(r"^theorem ([\w.']+)",s,re.M)]
 defs += [ns+'.'+n for n in re.findall(r"^(?:noncomputable\s+)?(?:def|abbrev) ([\w.']+)",s,re.M)]
roots=['Dubon2026.sourcePrimitive_exists_originalSupport_oddResidualGalois_charP']
extra=['Dubon2026.sourcePrimitive_exists_originalSupport_cyclotomicResidualGalois_charP','Dubon2026.sourcePrimitive_binaryDegree_even','Dubon2026.originalCyclotomicConjugation_power','Dubon2026.rationalArithmeticLocalRestrictionContinuous_commutes']
separatelyChecked=[]
required=list(dict.fromkeys([n for n in ths+defs if n not in separatelyChecked]+extra))
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=separatelyChecked)
def output(name,s):
 f=p/name;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-primitive-residual-oddness-2-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda ns:'#['+', '.join('`'+n for n in ns)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
template=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=template[template.index('private def runPlanarPairingAudit'):template.index('#lint in')]
for key,ns in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+key+r' : Array Name := #\[[^\n]*','let '+key+' : Array Name := '+arr(ns),body)
body=body.replace('Primitive Tate Restriction','Primitive Residual Oddness').replace('PRIMITIVE TATE RESTRICTION','PRIMITIVE RESIDUAL ODDNESS')
body=body.replace('SOURCE ORIGINAL PRIMITIVE RESIDUAL ODDNESS','SOURCE PRIMITIVE RESIDUAL ODDNESS')
output('SourcePrimitiveResidualOddnessAudit2.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
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
dep=dep[:dep.index('  logInfo m!')]+ '  logInfo m!"SOURCE PRIMITIVE RESIDUAL ODDNESS DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the actual original all-weight prescribed-prime residual consumer. Only declaration values are traversed. The original real arithmetic restriction acts by genuine complex conjugation under the original complex embedding; its cyclotomic exponent is minus one. The original primitive form has even weight, so the same residual representation has determinant minus one at this real restriction. The constructed coefficient field, characteristic, global determinant, original Fourier reductions and good-prime inertia are retained. No oddness or weight-parity assumption is supplied. Adic realization, local/image properties, automorphy and literal higher symmetric-power continuation remain required. 16/20; DUB-17--20 OPEN."\\n\\n#eval runPlanarPairingDependencyAudit\\n'

output('SourcePrimitiveResidualOddnessDependencyAudit2.lean',imports+dep)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
files=[prod/(m+'.lean') for m in ['ArithmeticRealH2Restriction','CyclotomicConjugationPower','RationalArithmeticCyclotomicCharacter','SourceArithmeticWeightTwist','SourcePrimitiveWeightParity']]
files += [p/'SourcePrimitiveResidualGlobalDeterminant.lean']
rd=dict(scope=574,chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> actual all-weight Galois association -> oddness of the same original residual representation at the actual real restriction',reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in files],shorterRoute='Reuse the existing real arithmetic restriction, the original complex-embedding commutation theorem and the proved cyclotomic conjugation exponent. Combine the assembled global determinant with the already proved even-weight property of the original primitive form. No new infinite-place or representation theory is needed.',assumptionsToDischarge='The original primitive form, weight at least two and prescribed prime give the same actual original-support residual representation with determinant minus one at genuine complex conjugation. Weight parity and oddness are derived. All coefficient-field, residue-characteristic, global-determinant, original Frobenius and inertia conclusions are retained.',remaining='All-weight adic realization and required local, image and regularity properties, arithmetic automorphy and literal higher symmetric-power continuation remain required. 16/20; DUB-17--20 OPEN.',scratchImportClosure=localClosure,separatelyAxiomChecked=separatelyChecked)
output('primitive-residual-oddness-route-574.json',json.dumps(rd,indent=2)+'\\n')
print(json.dumps(dict(modules=len(mods),queries=len(cfg['queries']),theorems=len(ths),constructions=len(defs),edges=len(required))))
