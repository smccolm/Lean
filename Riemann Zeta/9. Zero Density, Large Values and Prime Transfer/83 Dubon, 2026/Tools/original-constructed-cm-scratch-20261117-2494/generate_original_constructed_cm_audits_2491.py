from pathlib import Path
import json,hashlib,re
s=Path(__file__).parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
pairs=[('SourceOriginalCMKernelConsequences2473b','SourceOriginalCMKernelConsequences'),('SourceOriginalRationalBottomRestriction2474d','SourceOriginalRationalBottomRestriction'),('SourceOriginalRationalCMProperty2475a','SourceOriginalRationalCMProperty'),('SourceGammaOneOriginalCMConsequences2476b','SourceGammaOneOriginalCMConsequences'),('SourceOriginalRationalBottomOdd2477b','SourceOriginalRationalBottomOdd'),('SourceOriginalRationalCMPolarized2478a','SourceOriginalRationalCMPolarized'),('SourceOriginalRationalCMPolarizationProperty2479a','SourceOriginalRationalCMPolarizationProperty'),('SourceGammaOneOriginalCMPolarized2484a','SourceGammaOneOriginalCMPolarized'),('SourceOriginalCMQuadraticField2485d','SourceOriginalCMQuadraticField'),('SourceOriginalSupportCyclotomic2486b','SourceOriginalSupportCyclotomic'),('SourceOriginalSupportResidual2487b','SourceOriginalSupportResidual'),('SourceOriginalConstructedCMProperty2488a','SourceOriginalConstructedCMProperty'),('SourceOriginalConstructedCMAssembly2489a','SourceOriginalConstructedCMAssembly'),('SourceGammaOneOriginalConstructedCM2490a','SourceGammaOneOriginalConstructedCM')]
old=json.loads((s/'source-original-torus-audit-config-2480.json').read_text())
substitutions=[(Path(r['source']).stem,r['module']) for r in old['files']]+pairs
c=dict(files=[],modules=[],queries=[],theorems=[],constructions=[],roots=[],proofEdges=[],scope='Actual original modular-form residual representation: native CM kernel consequences over the original coefficient field, polarized symmetric representations, and a constructed genuine CM field in support 4a. Original finite linear bounds are used through literal surjective support restriction. All previous data and the explicit small-image alternative remain.')
planned={}
for source,module in pairs:
 f=s/(source+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0',source
 assert f.with_suffix('.log').stat().st_size==0,source
 t=f.read_text(encoding='utf-8')
 for a,b in substitutions:t=re.sub(r'(?m)^import '+a+'$','import '+b,t)
 assert not (s/(module+'.lean')).exists(),module
 planned[module]=t
for row in old['files']:assert sha(Path(row['path']))==row['canonicalSha256']
def write(name,t):
 f=s/name;assert not f.exists(),name;f.write_text(t,encoding='utf-8')
for source,module in pairs:
 f=s/(source+'.lean');t=planned[module];write(module+'.lean',t);canonical=s/(module+'.lean')
 c['files'].append(dict(source=str(f),sourceSha256=sha(f),module=module,path=str(canonical),canonicalSha256=sha(canonical)))
 c['modules'].append(module)
 ns=re.search(r'(?m)^namespace (\S+)',t)[1]
 th=[ns+'.'+n for n in re.findall(r'(?m)^theorem (\S+)',t)]
 df=[ns+'.'+n for n in re.findall(r'(?m)^def (\S+)',t)]
 c['queries']+=th+df;c['theorems']+=th;c['constructions']+=df
assert len(c['modules'])==14
c['roots']=[c['theorems'][-1]]
c['proofEdges']=list(dict.fromkeys(old['proofEdges']+c['queries']+[
 'Dubon2026.finiteBaseCMSymmetricPolarizedRepresentation_kernel',
 'Dubon2026.finiteBaseCMSymmetricPolarizedRepresentation_component',
 'Dubon2026.finiteBaseCMSymmetricPolarizedRepresentation_odd',
 'Dubon2026.sourceArithmetic_real_det_of_cyclotomic',
 'Dubon2026.sourcePrimitive_weight_even',
 'Dubon2026.originalQUnramifiedUnion_exists_primitiveRoot',
 'Dubon2026.rationalArithmeticSupportRestriction_surjective',
 'Dubon2026.rationalArithmeticSupportRestriction_commutes',
 'Dubon2026.rationalArithmeticCyclotomicCharacter_apply_root',
 'IsCyclotomicExtension.finrank',
 'NumberField.InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt']))
c['sourceAssemblyReview']=json.loads((s/'original-constructed-cm-reuse-review-2491.json').read_text())
arr=lambda xs:'#['+', '.join('`'+n for n in xs)+']'
olddep=(s/'SourceOriginalTorusDependencyAudit2.lean').read_text(encoding='utf-8')
localmods=re.findall(r'`([A-Za-z0-9_.]+)',re.search(r'let localModules : Array Name := #\[(.*)\]',olddep)[1])+c['modules']
for a,b in [('SourceOriginalTorusAudit2','SourceOriginalConstructedCMAudit1'),('SourceOriginalTorusDependencyAudit2','SourceOriginalConstructedCMDependencyAudit1'),('SourceOriginalTorusDeclarations2480','SourceOriginalConstructedCMDeclarations2491')]:
 t=(s/(a+'.lean')).read_text(encoding='utf-8');t=re.sub(r'(?m)^import Source.*\n','',t);t='import '+c['modules'][-1]+'\n'+t
 if 'Audit' in a and 'Dependency' not in a:
  t=re.sub(r'(?m)^#print axioms .*\n','',t)
  t=t.replace('open Lean\n','open Lean\n\n'+'\n'.join('#print axioms '+q for q in c['queries'])+'\n',1)
  t=re.sub(r'let modules : Array Name := #\[.*\]','let modules : Array Name := '+arr(c['modules']),t)
  t=re.sub(r'(?m)^#lint in .*\n','',t);t+='\n'.join('#lint in '+m for m in c['modules'])+'\n'
  t=t.replace('SOURCE ORIGINAL TORUS AXIOM AUDIT PASS','SOURCE ORIGINAL CONSTRUCTED CM AXIOM AUDIT PASS')
 elif 'Dependency' in a:
  for label,values in [('roots',c['roots']),('localModules',localmods),('required',c['proofEdges'])]:
   t=re.sub('let '+label+r' : Array Name := #\[.*\]','let '+label+' : Array Name := '+arr(values),t)
  t=t.replace('SOURCE ORIGINAL TORUS VALUE AUDIT PASS','SOURCE ORIGINAL CONSTRUCTED CM VALUE AUDIT PASS')
 else:t=re.sub(r'let mods : Array Name := #\[.*\]','let mods : Array Name := '+arr(c['modules']),t)
 write(b+'.lean',t)
write('source-original-constructed-cm-audit-config-2491.json',json.dumps(c,indent=2)+'\n')
t=(s/'SourceOriginalTorusScratchSemantic2481.lean').read_text(encoding='utf-8')
t=re.sub(r'(?m)^import Source.*\n','',t);t='import '+c['modules'][-1]+'\n'+t
mods=re.findall(r'"([^"]+)"',re.search(r'private def moduleNames : Array String := #\[(.*)\]',t)[1])+c['modules']
for label,values in [('moduleNames',mods),('auditedModuleNames',c['modules'])]:
 t=re.sub('private def '+label+r' : Array String := #\[.*\]','private def '+label+' : Array String := #['+', '.join(json.dumps(x) for x in values)+']',t)
write('SourceOriginalConstructedCMScratchSemantic2492.lean',t)
t=re.sub(r'(?m)^import (Source\S+)',r'import Dubon2026.\1',t)
write('SourceOriginalConstructedCMProductionSemantic2492.lean',t)
lines=["$ErrorActionPreference='Stop'","$taskScratch='E:\\Lean\\.tmp\\dubon83'"]
for m in c['modules']:
 lines+=["& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name '"+m+"'",'if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}']
for m in ['SourceOriginalConstructedCMAudit1','SourceOriginalConstructedCMDependencyAudit1','SourceOriginalConstructedCMDeclarations2491','SourceOriginalConstructedCMScratchSemantic2492']:
 lines+=["& (Join-Path $taskScratch 'run_dickson_audit_2285.ps1') -Name '"+m+"'",'if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}']
write('build_original_constructed_cm_2491.ps1','\n'.join(lines)+'\n')
print(json.dumps(dict(modules=len(c['modules']),publicQueries=len(c['queries']),publicTheorems=len(c['theorems']),publicConstructions=len(c['constructions']),requiredEdges=len(c['proofEdges']))))
