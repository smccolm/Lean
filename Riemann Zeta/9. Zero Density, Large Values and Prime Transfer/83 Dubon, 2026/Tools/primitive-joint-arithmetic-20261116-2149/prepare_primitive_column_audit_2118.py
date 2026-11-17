from pathlib import Path
from datetime import datetime, timezone
import re, json, hashlib

p=Path(__file__).parent
src=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
seen=set(); versions=[]
def visit(n):
    if n in seen:return
    seen.add(n)
    for dep in re.findall(r'(?m)^import (\S+)',(p/(n+'.lean')).read_text(encoding='utf-8')):
        if '.' not in dep:visit(dep)
    versions.append(n)
visit('SourceGammaOnePrimitiveColumnDiamond2117b')
mapping={v:re.sub(r'\d+[a-z]$','',v) for v in versions}
modules=list(mapping.values());queries=[];theorems=[];constructions=[];files=[]
def output(name,t):
    f=p/name
    assert not f.exists(),f
    f.write_text(t,encoding='utf-8')
for v,m in mapping.items():
    f=p/(v+'.lean');t=f.read_text(encoding='utf-8')
    if v!=m:
        assert f.with_suffix('.exit').read_text().strip()=='0'
        assert f.with_suffix('.log').stat().st_size==0
    assert not (src/(m+'.lean')).exists()
    c=re.sub(r'(?m)^import (\S+)$',lambda x:'import '+mapping.get(x[1],x[1]),t)
    target=p/(m+'.lean')
    if target.exists():assert target.read_text(encoding='utf-8')==c
    else:output(m+'.lean',c)
    assert re.sub(r'(?m)^import .*\n','',t)==re.sub(r'(?m)^import .*\n','',c)
    ns=re.search(r'(?m)^namespace (\S+)',t)[1]+'.'
    qs=re.findall(r'(?m)^(?:noncomputable )?(theorem|lemma|def|abbrev|instance)\s+(\S+)',t)
    queries += [ns+n for k,n in qs]
    theorems += [ns+n for k,n in qs if k in ['theorem','lemma']]
    constructions += [ns+n for k,n in qs if k not in ['theorem','lemma']]
    files.append(dict(version=v,module=m,path=str(f),sourceSha256=sha(f),canonicalSha256=sha(target),mathematicalBodyIdentical=True))
ns='Dubon2026.SourceFunctionField.GammaOne.'
roots=[ns+n for n in ['binaryPrimitiveColumnBoundary_ker','binaryPrimitiveColumnBoundary_hecke','binaryPrimitiveColumnBoundary_diamond']]
unconsumed=[ns+n for n in ['binaryPrimitiveCuspBoundary_ker','binaryHeckeWord_parabolic_iff_primitive_boundary_zero','binaryPrimePowerHeckeWord_parabolic_iff_primitive_boundary_zero']]
edges=[n for n in theorems if n not in unconsumed]+['Dubon2026.sourceGammaOneDiamondH1_hom_apply','Dubon2026.sourceGammaOneDiamond_conj_mem','Dubon2026.SourceCuspBoundary.colRed_lift','Dubon2026.SourceCuspBoundary.exists_borel','Dubon2026.SourceCuspBoundary.exists_conj_of_col_congr']
cfg=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),modules=modules,queries=queries,theorems=theorems,constructions=constructions,roots=roots,proofEdges=edges,separatelyAxiomChecked=unconsumed+constructions,files=files,productionMutation=False,scope='Faithful original finite primitive boundary, native Hecke and diamond intertwining. Arithmetic Galois realization, original-character specialization, DUB-17--20 remain open.')
output('primitive-column-audit-config-2118.json',json.dumps(cfg,indent=2)+'\n')
imports='\n'.join('import '+m for m in modules)+'\nimport Mathlib.Tactic\n\nopen Lean\n\n'
def array(t,name,names):
    t,n=re.subn(r'(?m)^  let '+name+r' : Array Name := #\[.*$', '  let '+name+' : Array Name := #['+', '.join('`'+x for x in names)+']',t)
    assert n==1
    return t
for old,new in [('SourceGammaOneExactJointCharacterAudit2','SourceGammaOnePrimitiveColumnAudit1'),('SourceGammaOneExactJointCharacterDependencyAudit2','SourceGammaOnePrimitiveColumnDependencyAudit1'),('SourceGammaOneExactJointCharacterScratchOwnership2100','SourceGammaOnePrimitiveColumnScratchOwnership2118')]:
    t=(p/(old+'.lean')).read_text(encoding='utf-8');t=t[t.index('private def'):]
    t=t.replace('GammaOneExactJointCharacter','GammaOnePrimitiveColumn').replace('SOURCE GAMMAONE EXACT JOINT CHARACTER','SOURCE GAMMAONE PRIMITIVE COLUMN').replace('Marked algebraic chart','Primitive column')
    if 'Dependency' in old:
        for n,x in [('roots',roots),('localModules',modules),('required',edges)]:t=array(t,n,x)
        a,b=t.index('  logInfo m!'),t.index('\n\n#eval')
        t=t[:a]+'  logInfo m!"SOURCE GAMMAONE PRIMITIVE COLUMN DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the VALUE closure of the actual primitive boundary kernel, Hecke intertwining and diamond intertwining. Primitive widths, the two actual coset orbits, integral conjugates and representative comparison are consumed. Arithmetic realization and source gates remain OPEN."'+t[b:]
    elif 'Ownership' in old:t=array(t,'mods',modules)
    else:
        t=t[:t.index('\n#lint')]
        for n,x in [('modules',modules),('theorems',theorems),('constructions',constructions)]:t=array(t,n,x)
        t='\n'.join('#print axioms '+n for n in queries)+'\n\n'+t+'\n'+'\n'.join('#lint in '+m for m in modules)+'\n'
    output(new+'.lean',imports+t)
runner=r'''$ErrorActionPreference='Stop'
$env:ELAN_HOME='C:\Users\Naraphim\.elan'
$env:LEAN_PATH='E:\Lean\.tmp\dubon83'
$taskScratch='E:\Lean\.tmp\dubon83'
Set-Location -LiteralPath 'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension'
$taskConfig=Get-Content -LiteralPath (Join-Path $taskScratch 'primitive-column-audit-config-2118.json') -Raw | ConvertFrom-Json
foreach($taskName in $taskConfig.modules){
  $taskBase=Join-Path $taskScratch "$taskName-2118"
  if(Test-Path -LiteralPath "$taskBase.log"){throw 'Evidence exists'}
  & 'C:\Users\Naraphim\.elan\bin\lake.exe' env lean -DautoImplicit=false -R $taskScratch -o (Join-Path $taskScratch "$taskName.olean") (Join-Path $taskScratch "$taskName.lean") *> "$taskBase.log"
  $taskExit=$LASTEXITCODE
  $taskExit | Out-File -LiteralPath "$taskBase.exit" -Encoding ascii
  if($taskExit -ne 0 -or (Get-Item -LiteralPath "$taskBase.log").Length -ne 0){Get-Content -LiteralPath "$taskBase.log" -Encoding Unicode;exit 1}
  Write-Output "PASS: $taskName"
}
foreach($taskName in @('SourceGammaOnePrimitiveColumnAudit1','SourceGammaOnePrimitiveColumnDependencyAudit1','SourceGammaOnePrimitiveColumnScratchOwnership2118')){
  $taskBase=Join-Path $taskScratch $taskName
  if(Test-Path -LiteralPath "$taskBase.log"){throw 'Evidence exists'}
  & 'C:\Users\Naraphim\.elan\bin\lake.exe' env lean -DautoImplicit=false "$taskBase.lean" *> "$taskBase.log"
  $taskExit=$LASTEXITCODE
  $taskExit | Out-File -LiteralPath "$taskBase.exit" -Encoding ascii
  if($taskExit -ne 0 -or (Select-String -LiteralPath "$taskBase.log" -Pattern '(^|\s)(warning:|error(?:\(|:)|PANIC\b)|Try this:|sorryAx|Found [1-9]')){Get-Content -LiteralPath "$taskBase.log" -Encoding Unicode;exit 1}
  Write-Output "PASS: $taskName"
}
'''
output('build_primitive_column_audit_2118.ps1',runner)
print(json.dumps(dict(modules=len(modules),queries=len(queries),theorems=len(theorems),constructions=len(constructions),proofValueEdges=len(edges),productionMutation=False)))
