from pathlib import Path
import hashlib,json,re

s=Path(__file__).parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
old=json.loads((s/'source-original-symmetric-joint-audit-config-2383.json').read_text())
pairs=[
 ('SourceOriginalArithmeticRootKernel2391a','SourceOriginalArithmeticRootKernel'),
 ('SourceSubfieldProjectorSpan2392a','SourceSubfieldProjectorSpan'),
 ('SourceSubfieldRegularTrace2393a','SourceSubfieldRegularTrace'),
 ('SourceSubfieldRegularKernel2394a','SourceSubfieldRegularKernel'),
 ('SourceTraceZeroCoefficientEmbedding2395c','SourceTraceZeroCoefficientEmbedding'),
 ('SourceTraceZeroConjugacy2396c','SourceTraceZeroConjugacy'),
 ('SourceOriginalExtendedTraceTest2397b','SourceOriginalExtendedTraceTest'),
 ('SourceFiniteLinearOriginalRegularDetection2398b','SourceFiniteLinearOriginalRegularDetection'),
 ('SourceOriginalArithmeticRegularCocycle2399c','SourceOriginalArithmeticRegularCocycle'),
 ('SourceOriginalRegularPrimePredicates2402b','SourceOriginalRegularPrimePredicates'),
 ('SourceOriginalRegularPrimeAssembly2401e','SourceOriginalRegularPrimeAssembly'),
 ('SourceOriginalArithmeticRegularPrimes2400g','SourceOriginalArithmeticRegularPrimes'),
 ('SourceOriginalArithmeticRegularPrimeProperty2403a','SourceOriginalArithmeticRegularPrimeProperty'),
 ('SourceGammaOneOriginalRegularPrimes2404a','SourceGammaOneOriginalRegularPrimes'),
]
c=dict(files=[],modules=[],queries=[],theorems=[],constructions=[],roots=[],proofEdges=[],
 scope='Actual original-form regular auxiliary primes in the finite linear subfield branch. Nonzero original symmetric twisted classes are detected outside every finite set with original finite affine factor and local Frobenius, retaining all preceding arithmetic and symmetric consequences for the same residual witness.')
def write(name,t):
 f=s/name;assert not f.exists(),name;f.write_text(t,encoding='utf-8')
for source,module in pairs:
 f=s/(source+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0'
 assert f.with_suffix('.log').stat().st_size==0,source
 t=f.read_text(encoding='utf-8')
 for a,b in pairs:t=re.sub(r'(?m)^import '+a+'$', 'import '+b,t)
 write(module+'.lean',t)
 canonical=s/(module+'.lean')
 c['files'].append(dict(source=str(f),sourceSha256=sha(f),module=module,path=str(canonical),canonicalSha256=sha(canonical)))
 c['modules'].append(module)
 ns=re.search(r'(?m)^namespace (\S+)',t)[1]
 th=[ns+'.'+n for n in re.findall(r'(?m)^theorem (\S+)',t)]
 df=[ns+'.'+n for n in re.findall(r'(?m)^def (\S+)',t)]
 c['queries']+=th+df;c['theorems']+=th;c['constructions']+=df
assert (len(c['modules']),len(c['queries']),len(c['theorems']),len(c['constructions']))==(14,20,16,4)
c['roots']=[c['theorems'][-1]]
c['proofEdges']=list(dict.fromkeys(old['proofEdges']+c['queries']+[
 'Dubon2026.finiteSymmetric_projector_conjugates_span',
 'Dubon2026.finiteSymmetric_projector_invariant_eq_top',
 'Dubon2026.fullMatrixTracePairing_bijective',
 'Dubon2026.homogeneousSymmetricGL_unitDiagonal_separable',
 'Dubon2026.matrixTraceZero_traceFunctional_fixed',
 'Dubon2026.cocycle_exists_detecting_kernel_translate',
 'Dubon2026.rationalArithmetic_exists_regular_detecting_cocycle',
 'Dubon2026.rationalArithmetic_exists_cocycle_auxiliary_prime',
 'Dubon2026.rationalArithmetic_local_regular_detection_of_finite_factor',
 'Dubon2026.rationalArithmetic_local_detection_of_finite_factor',
 'Dubon2026.rationalArithmetic_exists_local_frobenius',
]))
c['sourceAssemblyReview']='The final source theorem unpacks the preceding actual-form symmetric/cohomology consumer, keeps its same residual witness and all its conclusions, and derives original regular detecting primes from its constructed finite linear subfield branch. The common finite affine factor is retained in full; the congruence q = 1 modulo p^(level+1) is stronger than the requested p^level congruence. No original class is replaced by a scalar-extended H1 class. Predicate definitions name the literal native statements and do not postulate them. Failed monolithic assemblies and diagnostic variants remain retained; default proof limits are unchanged.'
arr=lambda xs:'#['+', '.join('`'+n for n in xs)+']'
old_dependency=(s/'SourceOriginalSymmetricJointDependencyAudit1.lean').read_text(encoding='utf-8')
localmods=re.findall(r'`([A-Za-z0-9_.]+)',re.search(r'let localModules : Array Name := #\[(.*)\]',old_dependency)[1])+c['modules']
for a,b in [('SourceOriginalSymmetricJointAudit1','SourceOriginalRegularPrimeAudit1'),('SourceOriginalSymmetricJointDependencyAudit1','SourceOriginalRegularPrimeDependencyAudit1'),('SourceOriginalSymmetricJointDeclarations2383','SourceOriginalRegularPrimeDeclarations2405')]:
 t=(s/(a+'.lean')).read_text(encoding='utf-8');t=re.sub(r'(?m)^import Source.*\n','',t);t='import '+c['modules'][-1]+'\n'+t
 if a.endswith('Audit1') and 'Dependency' not in a:
  t=re.sub(r'(?m)^#print axioms .*\n','',t)
  t=t.replace('open Lean\n','open Lean\n\n'+'\n'.join('#print axioms '+q for q in c['queries'])+'\n',1)
  t=re.sub(r'let modules : Array Name := #\[.*\]','let modules : Array Name := '+arr(c['modules']),t)
  t=re.sub(r'(?m)^#lint in .*\n','',t);t+='\n'.join('#lint in '+m for m in c['modules'])+'\n'
  t=t.replace('SOURCE ORIGINAL SYMMETRIC JOINT AXIOM AUDIT PASS','SOURCE ORIGINAL REGULAR PRIME AXIOM AUDIT PASS')
 elif 'Dependency' in a:
  for label,values in [('roots',c['roots']),('localModules',localmods),('required',c['proofEdges'])]:
   t=re.sub('let '+label+r' : Array Name := #\[.*\]','let '+label+' : Array Name := '+arr(values),t)
  t=t.replace('SOURCE ORIGINAL SYMMETRIC JOINT VALUE AUDIT PASS','SOURCE ORIGINAL REGULAR PRIME VALUE AUDIT PASS')
 else:t=re.sub(r'let mods : Array Name := #\[.*\]','let mods : Array Name := '+arr(c['modules']),t)
 write(b+'.lean',t)
write('source-original-regular-prime-audit-config-2405.json',json.dumps(c,indent=2)+'\n')

# Use the same strict structural normalizer in both environments.
t=(s/'SourceOriginalSymmetricJointScratchSemantic2385.lean').read_text(encoding='utf-8')
t=re.sub(r'(?m)^import Source.*\n','',t);t='import '+c['modules'][-1]+'\n'+t
mods=re.findall(r'"([^"]+)"',re.search(r'private def moduleNames : Array String := #\[(.*)\]',t)[1])+c['modules']
for label,values in [('moduleNames',mods),('auditedModuleNames',c['modules'])]:
 t=re.sub('private def '+label+r' : Array String := #\[.*\]','private def '+label+' : Array String := #['+', '.join(json.dumps(x) for x in values)+']',t)
write('SourceOriginalRegularPrimeScratchSemantic2406.lean',t)
t=re.sub(r'(?m)^import (Source\S+)',r'import Dubon2026.\1',t)
write('SourceOriginalRegularPrimeProductionSemantic2406.lean',t)

lines=["$ErrorActionPreference='Stop'","$taskScratch='E:\\Lean\\.tmp\\dubon83'"]
for m in c['modules']:
 lines+= ["& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name '"+m+"'",'if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}']
for m in ['SourceOriginalRegularPrimeAudit1','SourceOriginalRegularPrimeDependencyAudit1','SourceOriginalRegularPrimeDeclarations2405','SourceOriginalRegularPrimeScratchSemantic2406']:
 lines+= ["& (Join-Path $taskScratch 'run_dickson_audit_2285.ps1') -Name '"+m+"'",'if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}']
write('build_original_regular_primes_2405.ps1','\n'.join(lines)+'\n')
print(json.dumps(dict(modules=14,publicQueries=20,publicTheorems=16,publicConstructions=4,requiredEdges=len(c['proofEdges']))))
