from pathlib import Path
import json,re,hashlib
p=Path(__file__).parent
prod=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
mods=['SourceArithmeticCharacterFrobeniusEquality','SourceResidualCyclotomicDeterminant','SourcePrimitiveResidualGlobalDeterminant']
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 s=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',f.read_text(encoding='utf-8'),flags=re.S))
 ns=re.search(r'^namespace (\S+)',s,re.M)[1]
 ths += [ns+'.'+n for n in re.findall(r"^theorem ([\w.']+)",s,re.M)]
 defs += [ns+'.'+n for n in re.findall(r"^(?:noncomputable\s+)?(?:def|abbrev) ([\w.']+)",s,re.M)]
roots=['Dubon2026.sourcePrimitive_exists_originalSupport_cyclotomicResidualGalois_charP']
extra=['Dubon2026.sourcePrimitive_exists_originalSupport_residualGalois_charP','Dubon2026.continuous_rational_galois_exists_frobenius_prime','Dubon2026.rationalPrimeOriginalNorm_exists_frobenius','Dubon2026.rationalArithmetic_original_residue_frobenius_class','Dubon2026.sourceArithmeticCyclotomicUnitCharacter_frobenius']
separatelyChecked=[]
required=list(dict.fromkeys([n for n in ths+defs if n not in separatelyChecked]+extra))
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=separatelyChecked)
def output(name,s):
 f=p/name;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-primitive-residual-determinant-3-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda ns:'#['+', '.join('`'+n for n in ns)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
template=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=template[template.index('private def runPlanarPairingAudit'):template.index('#lint in')]
for key,ns in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+key+r' : Array Name := #\[[^\n]*','let '+key+' : Array Name := '+arr(ns),body)
body=body.replace('Primitive Tate Restriction','Primitive Residual Determinant').replace('PRIMITIVE TATE RESTRICTION','PRIMITIVE RESIDUAL DETERMINANT')
body=body.replace('SOURCE ORIGINAL PRIMITIVE RESIDUAL DETERMINANT','SOURCE PRIMITIVE RESIDUAL DETERMINANT')
output('SourcePrimitiveResidualDeterminantAudit3.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
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
dep=dep[:dep.index('  logInfo m!')]+ '  logInfo m!"SOURCE PRIMITIVE RESIDUAL DETERMINANT DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the actual original all-weight prescribed-prime residual consumer. Only declaration values are traversed. Existing finite-factor Chebotarev and actual norm-residue Frobenius lifting identify continuous characters from good-prime values. The already constructed representation has global determinant equal to the original cyclotomic character to power k-1, while preserving its original Fourier reductions, arithmetic support, local coefficient field and inertia. Global determinant compatibility is derived, not assumed. All-weight adic realization, local/image properties, automorphy and literal higher symmetric-power continuation remain open. 16/20; DUB-17--20 OPEN."\\n\\n#eval runPlanarPairingDependencyAudit\\n'

output('SourcePrimitiveResidualDeterminantDependencyAudit3.lean',imports+dep)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
files=[prod/(m+'.lean') for m in ['ChebotarevRationalPrime','RationalArithmeticNormFrobenius','RationalPrimeFiniteTameGenerator','SourceArithmeticWeightTwist']]
files += [p/'SourcePrimitiveResidualGaloisCharP.lean']
rd=dict(scope=572,chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> actual all-weight Galois association with fixed determinant -> global cyclotomic determinant of the same original residual representation',reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in files],shorterRoute='Reuse the existing finite-factor Chebotarev theorem and actual norm-residue Frobenius lift to compare the determinant and cyclotomic characters. No new density theorem or Galois topology is needed. Apply this to the same representation returned by the completed original-support prescribed-prime residual consumer.',assumptionsToDischarge='Global determinant compatibility is proved from the exact original good-prime Frobenius determinant. The terminal consumer starts with the original primitive form, weight at least two and prescribed rational prime; it constructs the local field and residue characteristic, retains original Fourier traces and good-prime inertia, and proves determinant equals the original cyclotomic character to power k-1.',remaining='All-weight adic realization and required local, image and regularity properties, arithmetic automorphy and literal higher symmetric-power continuation remain required. 16/20; DUB-17--20 OPEN.',scratchImportClosure=localClosure,separatelyAxiomChecked=separatelyChecked)
output('primitive-residual-determinant-route-572.json',json.dumps(rd,indent=2)+'\\n')
print(json.dumps(dict(modules=len(mods),queries=len(cfg['queries']),theorems=len(ths),constructions=len(defs),edges=len(required))))
