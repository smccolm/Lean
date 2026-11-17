from pathlib import Path
import hashlib,json,re

s=Path(__file__).parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
old=json.loads((s/'source-original-detecting-family-audit-config-2427.json').read_text())
pairs=[('SourceOriginalLocalCoefficientH1Finite2422b', 'SourceOriginalLocalCoefficientH1Finite'), ('SourceOriginalLocalUnramifiedDimension2423b', 'SourceOriginalLocalUnramifiedDimension'), ('SourceOriginalPrimeUnramifiedDimension2424a', 'SourceOriginalPrimeUnramifiedDimension'), ('SourceOriginalUnramifiedAdjointProperty2425c', 'SourceOriginalUnramifiedAdjointProperty'), ('SourceGammaOneOriginalUnramifiedDimensions2426b', 'SourceGammaOneOriginalUnramifiedDimensions')]

c=dict(files=[],modules=[],queries=[],theorems=[],constructions=[],roots=[],proofEdges=[],
 scope='Actual original local unramified adjoint H1/invariant dimension comparison for every symmetric degree and every rational prime, preserving the same actual residual action, all arithmetic data and the preceding bounded detecting-family alternative.')
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
assert (len(c['modules']),len(c['queries']),len(c['theorems']),len(c['constructions']))==(5,7,6,1)
c['roots']=[c['theorems'][-1]]
c['proofEdges']=list(dict.fromkeys(old['proofEdges']+c['queries']+[
 'Dubon2026.localField_finiteCoefficientCocycles',
 'Dubon2026.continuous_unramified_finrank_eq_invariants_of_cyclic_depth',
 'Dubon2026.algebraicLocal_frobenius_generates_inertia_quotient',
 'Dubon2026.algebraicLocal_exists_inertia_quotient_card_dvd',
 'Dubon2026.algebraicLocal_exists_residueFrobenius',
 'Dubon2026.normLocal_residue_finite',
]))
c['sourceAssemblyReview']='Original local coefficient finiteness follows from scalar restriction on the same action and continuous cocycles. Native general-field cyclic-depth comparison constructs the original unramified H1/invariant equality; actual local arithmetic supplies every depth, residue and Frobenius input. The final actual-form consumer retains all previous data and adds the comparison on every symmetric adjoint at every rational prime. No original prime-field equality, supplied H1 finiteness or supplied local cyclicity hypothesis remains. The numerical regular-prime invariant dimension and remaining local deformation conditions are still open. Default limits and all linters remain unchanged.'

arr=lambda xs:'#['+', '.join('`'+n for n in xs)+']'
old_dependency=(s/'SourceOriginalDetectingFamilyDependencyAudit2.lean').read_text(encoding='utf-8')
localmods=re.findall(r'`([A-Za-z0-9_.]+)',re.search(r'let localModules : Array Name := #\[(.*)\]',old_dependency)[1])+c['modules']
for a,b in [('SourceOriginalDetectingFamilyAudit2','SourceOriginalUnramifiedDimensionAudit1'),('SourceOriginalDetectingFamilyDependencyAudit2','SourceOriginalUnramifiedDimensionDependencyAudit1'),('SourceOriginalDetectingFamilyDeclarations2427','SourceOriginalUnramifiedDimensionDeclarations2434')]:
 t=(s/(a+'.lean')).read_text(encoding='utf-8');t=re.sub(r'(?m)^import Source.*\n','',t);t='import '+c['modules'][-1]+'\n'+t
 if a.endswith('Audit1') and 'Dependency' not in a:
  t=re.sub(r'(?m)^#print axioms .*\n','',t)
  t=t.replace('open Lean\n','open Lean\n\n'+'\n'.join('#print axioms '+q for q in c['queries'])+'\n',1)
  t=re.sub(r'let modules : Array Name := #\[.*\]','let modules : Array Name := '+arr(c['modules']),t)
  t=re.sub(r'(?m)^#lint in .*\n','',t);t+='\n'.join('#lint in '+m for m in c['modules'])+'\n'
  t=t.replace('SOURCE ORIGINAL DETECTING FAMILY AXIOM AUDIT PASS','SOURCE ORIGINAL UNRAMIFIED DIMENSION AXIOM AUDIT PASS')
 elif 'Dependency' in a:
  for label,values in [('roots',c['roots']),('localModules',localmods),('required',c['proofEdges'])]:
   t=re.sub('let '+label+r' : Array Name := #\[.*\]','let '+label+' : Array Name := '+arr(values),t)
  t=t.replace('SOURCE ORIGINAL DETECTING FAMILY VALUE AUDIT PASS','SOURCE ORIGINAL UNRAMIFIED DIMENSION VALUE AUDIT PASS')
 else:t=re.sub(r'let mods : Array Name := #\[.*\]','let mods : Array Name := '+arr(c['modules']),t)
 write(b+'.lean',t)
write('source-original-unramified-dimension-audit-config-2434.json',json.dumps(c,indent=2)+'\n')

# Use the same strict structural normalizer in both environments.
t=(s/'SourceOriginalDetectingFamilyScratchSemantic2428.lean').read_text(encoding='utf-8')
t=re.sub(r'(?m)^import Source.*\n','',t);t='import '+c['modules'][-1]+'\n'+t
mods=re.findall(r'"([^"]+)"',re.search(r'private def moduleNames : Array String := #\[(.*)\]',t)[1])+c['modules']
for label,values in [('moduleNames',mods),('auditedModuleNames',c['modules'])]:
 t=re.sub('private def '+label+r' : Array String := #\[.*\]','private def '+label+' : Array String := #['+', '.join(json.dumps(x) for x in values)+']',t)
write('SourceOriginalUnramifiedDimensionScratchSemantic2435.lean',t)
t=re.sub(r'(?m)^import (Source\S+)',r'import Dubon2026.\1',t)
write('SourceOriginalUnramifiedDimensionProductionSemantic2435.lean',t)

lines=["$ErrorActionPreference='Stop'","$taskScratch='E:\\Lean\\.tmp\\dubon83'"]
for m in c['modules']:
 lines+= ["& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name '"+m+"'",'if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}']
for m in ['SourceOriginalUnramifiedDimensionAudit1','SourceOriginalUnramifiedDimensionDependencyAudit1','SourceOriginalUnramifiedDimensionDeclarations2434','SourceOriginalUnramifiedDimensionScratchSemantic2435']:
 lines+= ["& (Join-Path $taskScratch 'run_dickson_audit_2285.ps1') -Name '"+m+"'",'if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}']
write('build_original_unramified_dimensions_2434.ps1','\n'.join(lines)+'\n')
print(json.dumps(dict(modules=5,publicQueries=7,publicTheorems=6,publicConstructions=1,requiredEdges=len(c['proofEdges']))))
