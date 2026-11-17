from pathlib import Path
import hashlib,json,re

s=Path(__file__).parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
old=json.loads((s/'source-original-unramified-dimension-audit-config-2434.json').read_text())
pairs=[('SourceOriginalDistinctEigenbasis2432b', 'SourceOriginalDistinctEigenbasis'), ('SourceOriginalDiagonalConjugacy2433a', 'SourceOriginalDiagonalConjugacy'), ('SourceOriginalMappedDistinctRoots2439e', 'SourceOriginalMappedDistinctRoots'), ('SourcePrimeSubfieldSL2Image2440b', 'SourcePrimeSubfieldSL2Image'), ('SourceOriginalMappedTorusConjugacy2442c', 'SourceOriginalMappedTorusConjugacy'), ('SourceOriginalSymmetricTorusRoots2444a', 'SourceOriginalSymmetricTorusRoots'), ('SourceOriginalSymmetricTorusConjugacy2445a', 'SourceOriginalSymmetricTorusConjugacy'), ('SourceFiniteLinearOriginalTorusDetection2443b', 'SourceFiniteLinearOriginalTorusDetection'), ('SourceOriginalArithmeticTorusCocycle2446b', 'SourceOriginalArithmeticTorusCocycle'), ('SourceOriginalTorusPrimeLocalProperties2459a', 'SourceOriginalTorusPrimeLocalProperties'), ('SourceOriginalTorusPrimePredicates2447b', 'SourceOriginalTorusPrimePredicates'), ('SourceOriginalTorusDetectionPredicate2453b', 'SourceOriginalTorusDetectionPredicate'), ('SourceOriginalPrimeTorusDimension2448a', 'SourceOriginalPrimeTorusDimension'), ('SourceOriginalAffineTorusDimension2458a', 'SourceOriginalAffineTorusDimension'), ('SourceOriginalTorusDetectionAssembly2454c', 'SourceOriginalTorusDetectionAssembly'), ('SourceOriginalTorusPrimeDimensions2455e', 'SourceOriginalTorusPrimeDimensions'), ('SourceOriginalTorusPrimeAssembly2449e', 'SourceOriginalTorusPrimeAssembly'), ('SourceOriginalArithmeticTorusPrimes2450b', 'SourceOriginalArithmeticTorusPrimes'), ('SourceOriginalArithmeticTorusPrimeProperty2451b', 'SourceOriginalArithmeticTorusPrimeProperty'), ('SourceGammaOneOriginalTorusPrimes2452b', 'SourceGammaOneOriginalTorusPrimes'), ('SourceOriginalTorusClassPredicates2461a', 'SourceOriginalTorusClassPredicates'), ('SourceOriginalTorusCocycleClass2462a', 'SourceOriginalTorusCocycleClass'), ('SourceOriginalTorusClassPrimes2463a', 'SourceOriginalTorusClassPrimes'), ('SourceOriginalTorusFamilyProperty2464a', 'SourceOriginalTorusFamilyProperty'), ('SourceOriginalTorusDetectingFamily2465a', 'SourceOriginalTorusDetectingFamily'), ('SourceOriginalArithmeticTorusFamilies2466b', 'SourceOriginalArithmeticTorusFamilies'), ('SourceGammaOneOriginalTorusFamilies2467b', 'SourceGammaOneOriginalTorusFamilies')]

c=dict(files=[],modules=[],queries=[],theorems=[],constructions=[],roots=[],proofEdges=[],
 scope='Same original residual representation: original split-torus detecting primes with exact unramified trace-zero adjoint H1 dimension equal to the symmetric degree, and bounded jointly detecting families with that dimension at every selected prime. The explicit small-image alternative and every earlier original arithmetic, symmetric and cohomological conclusion are retained.')
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
assert (len(c['modules']),len(c['queries']),len(c['theorems']),len(c['constructions']))==(27,34,23,11)
c['roots']=[c['theorems'][-1]]
c['proofEdges']=list(dict.fromkeys(old['proofEdges']+c['queries']+['Dubon2026.matrixTrace_invariants_finrank_of_symmetric_generator', 'Dubon2026.rationalArithmetic_local_frobenius_generates_representation_image', 'Dubon2026.rationalArithmetic_exists_conjugate_detecting_cocycle', "Module.End.eigenvectors_linearIndependent'"]))
c['sourceAssemblyReview']='The actual finite linear subfield lower bound contains the canonical prime-field SL2. Its regular torus has order p-1 and eigenvalues already in the original residue field. Native distinct-eigenvector independence and basis construction produce the original diagonalizer without a general scalar-extension theorem for H1 or invariant kernels. The original root-fixing cocycle and native conjugate Chebotarev preserve one actual finite factor and local Frobenius. Native cyclic-image generation, symmetric trace invariants and the proved original-field unramified H1 comparison give exact local dimension n. Original H1 finiteness and native finite detecting families then give the bounded family. All apply to the same actual original modular-form residual witness. Small-image exclusions, remaining local deformation conditions, automorphy and literal higher continuation remain open. Default proof limits, pins and all linters are unchanged.'

arr=lambda xs:'#['+', '.join('`'+n for n in xs)+']'
old_dependency=(s/'SourceOriginalUnramifiedDimensionDependencyAudit1.lean').read_text(encoding='utf-8')
localmods=re.findall(r'`([A-Za-z0-9_.]+)',re.search(r'let localModules : Array Name := #\[(.*)\]',old_dependency)[1])+c['modules']
for a,b in [('SourceOriginalUnramifiedDimensionAudit2','SourceOriginalTorusAudit1'),('SourceOriginalUnramifiedDimensionDependencyAudit1','SourceOriginalTorusDependencyAudit1'),('SourceOriginalUnramifiedDimensionDeclarations2434','SourceOriginalTorusDeclarations2469')]:
 t=(s/(a+'.lean')).read_text(encoding='utf-8');t=re.sub(r'(?m)^import Source.*\n','',t);t='import '+c['modules'][-1]+'\n'+t
 if 'Audit' in a and 'Dependency' not in a:
  t=re.sub(r'(?m)^#print axioms .*\n','',t)
  t=t.replace('open Lean\n','open Lean\n\n'+'\n'.join('#print axioms '+q for q in c['queries'])+'\n',1)
  t=re.sub(r'let modules : Array Name := #\[.*\]','let modules : Array Name := '+arr(c['modules']),t)
  t=re.sub(r'(?m)^#lint in .*\n','',t);t+='\n'.join('#lint in '+m for m in c['modules'])+'\n'
  t=t.replace('SOURCE ORIGINAL UNRAMIFIED DIMENSION AXIOM AUDIT PASS','SOURCE ORIGINAL TORUS AXIOM AUDIT PASS')
 elif 'Dependency' in a:
  for label,values in [('roots',c['roots']),('localModules',localmods),('required',c['proofEdges'])]:
   t=re.sub('let '+label+r' : Array Name := #\[.*\]','let '+label+' : Array Name := '+arr(values),t)
  t=t.replace('SOURCE ORIGINAL UNRAMIFIED DIMENSION VALUE AUDIT PASS','SOURCE ORIGINAL TORUS VALUE AUDIT PASS')
 else:t=re.sub(r'let mods : Array Name := #\[.*\]','let mods : Array Name := '+arr(c['modules']),t)
 write(b+'.lean',t)
write('source-original-torus-audit-config-2469.json',json.dumps(c,indent=2)+'\n')

# Use the same strict structural normalizer in both environments.
t=(s/'SourceOriginalUnramifiedDimensionScratchSemantic2435.lean').read_text(encoding='utf-8')
t=re.sub(r'(?m)^import Source.*\n','',t);t='import '+c['modules'][-1]+'\n'+t
mods=re.findall(r'"([^"]+)"',re.search(r'private def moduleNames : Array String := #\[(.*)\]',t)[1])+c['modules']
for label,values in [('moduleNames',mods),('auditedModuleNames',c['modules'])]:
 t=re.sub('private def '+label+r' : Array String := #\[.*\]','private def '+label+' : Array String := #['+', '.join(json.dumps(x) for x in values)+']',t)
write('SourceOriginalTorusScratchSemantic2470.lean',t)
t=re.sub(r'(?m)^import (Source\S+)',r'import Dubon2026.\1',t)
write('SourceOriginalTorusProductionSemantic2470.lean',t)

lines=["$ErrorActionPreference='Stop'","$taskScratch='E:\\Lean\\.tmp\\dubon83'"]
for m in c['modules']:
 lines+= ["& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name '"+m+"'",'if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}']
for m in ['SourceOriginalTorusAudit1','SourceOriginalTorusDependencyAudit1','SourceOriginalTorusDeclarations2469','SourceOriginalTorusScratchSemantic2470']:
 lines+= ["& (Join-Path $taskScratch 'run_dickson_audit_2285.ps1') -Name '"+m+"'",'if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}']
write('build_original_torus_2469.ps1','\n'.join(lines)+'\n')
print(json.dumps(dict(modules=27,publicQueries=34,publicTheorems=23,publicConstructions=11,requiredEdges=len(c['proofEdges']))))
