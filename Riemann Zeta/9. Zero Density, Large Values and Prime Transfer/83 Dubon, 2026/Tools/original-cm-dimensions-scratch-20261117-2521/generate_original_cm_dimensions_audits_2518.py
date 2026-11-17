from pathlib import Path
import json,hashlib,re
s=Path(__file__).parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
pairs=[('SourceOriginalCMAdjointVanishing2502a', 'SourceOriginalCMAdjointVanishing'), ('SourceOriginalCMCotangent2505a', 'SourceOriginalCMCotangent'), ('SourceOriginalCMCotangentFormula2508a', 'SourceOriginalCMCotangentFormula'), ('SourceOriginalIntegralCMDimensionData2509a', 'SourceOriginalIntegralCMDimensionData'), ('SourceOriginalSupportBottomBounds2516b', 'SourceOriginalSupportBottomBounds'), ('SourceOriginalIntegralCMDimensionField2512c', 'SourceOriginalIntegralCMDimensionField'), ('SourceOriginalIntegralCMDimensionProperty2513c', 'SourceOriginalIntegralCMDimensionProperty'), ('SourceOriginalIntegralCMDimensionAssembly2514c', 'SourceOriginalIntegralCMDimensionAssembly'), ('SourceGammaOneOriginalCMDimensions2515c', 'SourceGammaOneOriginalCMDimensions')]
old=json.loads((s/'source-original-integral-cm-audit-config-2506.json').read_text())
substitutions=[(Path(r['source']).stem,r['module']) for r in old['files']]+pairs
c=dict(files=[],modules=[],queries=[],theorems=[],constructions=[],roots=[],proofEdges=[],scope='The same actual original modular-form integral/residual pair has native CM deformation rings with full-adjoint H0 zero and exact cotangent dimension on the original finite linear subfield branch. The actual original integral multiplier and native ring are consumed together; every prior conclusion and the explicit small-image alternative remain.')
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
assert len(c['modules'])==9
c['roots']=[c['theorems'][-1]]
c['proofEdges']=list(dict.fromkeys(old['proofEdges']+c['queries']+['Dubon2026.finiteBasePolarizedCotangent_finrank_add_invariants','Dubon2026.matrixAdjointInvariant_eq_scalar_of_extension','Dubon2026.polarizedAdjoint_scalar_nonidentity']))
c['sourceAssemblyReview']=json.loads((s/'original-cm-dimensions-reuse-review-2518.json').read_text())
arr=lambda xs:'#['+', '.join('`'+n for n in xs)+']'
olddep=(s/'SourceOriginalIntegralCMDependencyAudit1.lean').read_text(encoding='utf-8')
localmods=re.findall(r'`([A-Za-z0-9_.]+)',re.search(r'let localModules : Array Name := #\[(.*)\]',olddep)[1])+c['modules']
for a,b in [('SourceOriginalIntegralCMAudit1','SourceOriginalCMDimensionsAudit1'),('SourceOriginalIntegralCMDependencyAudit1','SourceOriginalCMDimensionsDependencyAudit1'),('SourceOriginalIntegralCMDeclarations2506','SourceOriginalCMDimensionsDeclarations2518')]:
 t=(s/(a+'.lean')).read_text(encoding='utf-8');t=re.sub(r'(?m)^import Source.*\n','',t);t='import '+c['modules'][-1]+'\n'+t
 if 'Audit' in a and 'Dependency' not in a:
  t=re.sub(r'(?m)^#print axioms .*\n','',t)
  t=t.replace('open Lean\n','open Lean\n\n'+'\n'.join('#print axioms '+q for q in c['queries'])+'\n',1)
  t=re.sub(r'let modules : Array Name := #\[.*\]','let modules : Array Name := '+arr(c['modules']),t)
  t=re.sub(r'(?m)^#lint in .*\n','',t);t+='\n'.join('#lint in '+m for m in c['modules'])+'\n'
  t=t.replace('SOURCE ORIGINAL INTEGRAL CM AXIOM AUDIT PASS','SOURCE ORIGINAL CM DIMENSIONS AXIOM AUDIT PASS')
 elif 'Dependency' in a:
  for label,values in [('roots',c['roots']),('localModules',localmods),('required',c['proofEdges'])]:
   t=re.sub('let '+label+r' : Array Name := #\[.*\]','let '+label+' : Array Name := '+arr(values),t)
  t=t.replace('SOURCE ORIGINAL INTEGRAL CM VALUE AUDIT PASS','SOURCE ORIGINAL CM DIMENSIONS VALUE AUDIT PASS')
 else:t=re.sub(r'let mods : Array Name := #\[.*\]','let mods : Array Name := '+arr(c['modules']),t)
 write(b+'.lean',t)
write('source-original-cm-dimensions-audit-config-2518.json',json.dumps(c,indent=2)+'\n')
t=(s/'SourceOriginalIntegralCMScratchSemantic2507.lean').read_text(encoding='utf-8')
t=re.sub(r'(?m)^import Source.*\n','',t);t='import '+c['modules'][-1]+'\n'+t
mods=re.findall(r'"([^"]+)"',re.search(r'private def moduleNames : Array String := #\[(.*)\]',t)[1])+c['modules']
for label,values in [('moduleNames',mods),('auditedModuleNames',c['modules'])]:
 t=re.sub('private def '+label+r' : Array String := #\[.*\]','private def '+label+' : Array String := #['+', '.join(json.dumps(x) for x in values)+']',t)
write('SourceOriginalCMDimensionsScratchSemantic2519.lean',t)
t=re.sub(r'(?m)^import (Source\S+)',r'import Dubon2026.\1',t)
write('SourceOriginalCMDimensionsProductionSemantic2519.lean',t)
lines=["$ErrorActionPreference='Stop'","$taskScratch='E:\\Lean\\.tmp\\dubon83'"]
for m in c['modules']:
 lines+=["& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name '"+m+"'",'if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}']
for m in ['SourceOriginalCMDimensionsAudit1','SourceOriginalCMDimensionsDependencyAudit1','SourceOriginalCMDimensionsDeclarations2518','SourceOriginalCMDimensionsScratchSemantic2519']:
 lines+=["& (Join-Path $taskScratch 'run_dickson_audit_2285.ps1') -Name '"+m+"'",'if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}']
write('build_original_cm_dimensions_2518.ps1','\n'.join(lines)+'\n')
print(json.dumps(dict(modules=len(c['modules']),publicQueries=len(c['queries']),publicTheorems=len(c['theorems']),publicConstructions=len(c['constructions']),requiredEdges=len(c['proofEdges']))))
