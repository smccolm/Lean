from pathlib import Path
import hashlib,json,re

s=Path(__file__).parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
old=json.loads((s/'source-original-regular-prime-audit-config-2405.json').read_text())
pairs=[('SourceOriginalCoefficientH1Finite2409b', 'SourceOriginalCoefficientH1Finite'), ('SourceOriginalClassPrimePredicates2412a', 'SourceOriginalClassPrimePredicates'), ('SourceOriginalCocycleClassPrimes2414a', 'SourceOriginalCocycleClassPrimes'), ('SourceOriginalClassRegularPrimes2410c', 'SourceOriginalClassRegularPrimes'), ('SourceOriginalDetectingFamilyProperty2413a', 'SourceOriginalDetectingFamilyProperty'), ('SourcePrimeIndexedDetectingFamily2416a', 'SourcePrimeIndexedDetectingFamily'), ('SourceOriginalFiniteDetectingFamily2411d', 'SourceOriginalFiniteDetectingFamily'), ('SourceOriginalArithmeticFamilyProperty2415b', 'SourceOriginalArithmeticFamilyProperty'), ('SourceGammaOneOriginalDetectingFamilies2417a', 'SourceGammaOneOriginalDetectingFamilies')]

c=dict(files=[],modules=[],queries=[],theorems=[],constructions=[],roots=[],proofEdges=[],
 scope='Actual original-form dimension-bounded detecting families on every original symmetric twisted H1 subspace. Global finiteness is derived by restricting coefficient scalars on the same cocycles, and the native finite-family theorem constructs joint injectivity. All preceding arithmetic and symmetric conclusions remain for the same residual witness.')
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
assert (len(c['modules']),len(c['queries']),len(c['theorems']),len(c['constructions']))==(9,13,8,5)
c['roots']=[c['theorems'][-1]]
c['proofEdges']=list(dict.fromkeys(old['proofEdges']+c['queries']+[
 'Dubon2026.rationalArithmeticFiniteCoefficientCocycles_finite',
 'Dubon2026.finite_detecting_family_of_pointwise',
]))
c['sourceAssemblyReview']='The final source theorem unpacks the preceding actual original regular-prime consumer, keeps the same residual witness and all conclusions, and proves a bounded jointly detecting family on every actual original H1 subspace. Finiteness comes from an injection of the same cocycles under prime-field scalar restriction, not an assumed cohomology comparison. Native dimension induction is reused. Failed monolithic elaboration attempts and unexecuted drafts are retained; proof limits remain unchanged.'

arr=lambda xs:'#['+', '.join('`'+n for n in xs)+']'
old_dependency=(s/'SourceOriginalRegularPrimeDependencyAudit1.lean').read_text(encoding='utf-8')
localmods=re.findall(r'`([A-Za-z0-9_.]+)',re.search(r'let localModules : Array Name := #\[(.*)\]',old_dependency)[1])+c['modules']
for a,b in [('SourceOriginalRegularPrimeAudit1','SourceOriginalDetectingFamilyAudit1'),('SourceOriginalRegularPrimeDependencyAudit1','SourceOriginalDetectingFamilyDependencyAudit1'),('SourceOriginalRegularPrimeDeclarations2405','SourceOriginalDetectingFamilyDeclarations2418')]:
 t=(s/(a+'.lean')).read_text(encoding='utf-8');t=re.sub(r'(?m)^import Source.*\n','',t);t='import '+c['modules'][-1]+'\n'+t
 if a.endswith('Audit1') and 'Dependency' not in a:
  t=re.sub(r'(?m)^#print axioms .*\n','',t)
  t=t.replace('open Lean\n','open Lean\n\n'+'\n'.join('#print axioms '+q for q in c['queries'])+'\n',1)
  t=re.sub(r'let modules : Array Name := #\[.*\]','let modules : Array Name := '+arr(c['modules']),t)
  t=re.sub(r'(?m)^#lint in .*\n','',t);t+='\n'.join('#lint in '+m for m in c['modules'])+'\n'
  t=t.replace('SOURCE ORIGINAL REGULAR PRIME AXIOM AUDIT PASS','SOURCE ORIGINAL DETECTING FAMILY AXIOM AUDIT PASS')
 elif 'Dependency' in a:
  for label,values in [('roots',c['roots']),('localModules',localmods),('required',c['proofEdges'])]:
   t=re.sub('let '+label+r' : Array Name := #\[.*\]','let '+label+' : Array Name := '+arr(values),t)
  t=t.replace('SOURCE ORIGINAL REGULAR PRIME VALUE AUDIT PASS','SOURCE ORIGINAL DETECTING FAMILY VALUE AUDIT PASS')
 else:t=re.sub(r'let mods : Array Name := #\[.*\]','let mods : Array Name := '+arr(c['modules']),t)
 write(b+'.lean',t)
write('source-original-detecting-family-audit-config-2418.json',json.dumps(c,indent=2)+'\n')

# Use the same strict structural normalizer in both environments.
t=(s/'SourceOriginalRegularPrimeScratchSemantic2406.lean').read_text(encoding='utf-8')
t=re.sub(r'(?m)^import Source.*\n','',t);t='import '+c['modules'][-1]+'\n'+t
mods=re.findall(r'"([^"]+)"',re.search(r'private def moduleNames : Array String := #\[(.*)\]',t)[1])+c['modules']
for label,values in [('moduleNames',mods),('auditedModuleNames',c['modules'])]:
 t=re.sub('private def '+label+r' : Array String := #\[.*\]','private def '+label+' : Array String := #['+', '.join(json.dumps(x) for x in values)+']',t)
write('SourceOriginalDetectingFamilyScratchSemantic2419.lean',t)
t=re.sub(r'(?m)^import (Source\S+)',r'import Dubon2026.\1',t)
write('SourceOriginalDetectingFamilyProductionSemantic2419.lean',t)

lines=["$ErrorActionPreference='Stop'","$taskScratch='E:\\Lean\\.tmp\\dubon83'"]
for m in c['modules']:
 lines+= ["& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name '"+m+"'",'if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}']
for m in ['SourceOriginalDetectingFamilyAudit1','SourceOriginalDetectingFamilyDependencyAudit1','SourceOriginalDetectingFamilyDeclarations2418','SourceOriginalDetectingFamilyScratchSemantic2419']:
 lines+= ["& (Join-Path $taskScratch 'run_dickson_audit_2285.ps1') -Name '"+m+"'",'if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}']
write('build_original_detecting_families_2418.ps1','\n'.join(lines)+'\n')
print(json.dumps(dict(modules=9,publicQueries=13,publicTheorems=8,publicConstructions=5,requiredEdges=len(c['proofEdges']))))
