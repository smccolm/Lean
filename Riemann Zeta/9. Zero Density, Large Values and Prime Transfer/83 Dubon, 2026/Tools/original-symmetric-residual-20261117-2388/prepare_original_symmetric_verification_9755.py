from pathlib import Path
import ast,json,re

p=Path(__file__).parent
def write(name,text):
    f=p/name;assert not f.exists(),name
    if f.suffix=='.py':ast.parse(text)
    f.write_text(text,encoding='utf-8')

def rename(t):
    return (t.replace('9725','9755').replace('9697','9725')
        .replace('source-projective-residual-image','source-original-symmetric-residual')
        .replace('SourceProjectiveResidualImage','SourceOriginalSymmetricResidual')
        .replace('appliedSourceOriginalRankTwo','appliedSourceProjectiveResidualImage')
        .replace('source-projective-semantic','source-original-symmetric-semantic'))

t=rename((p/'prepare_projective_residual_image_production_ownership_9725.py').read_text(encoding='utf-8'))
write('prepare_original_symmetric_residual_production_ownership_9755.py',t)
t=rename((p/'prepare_projective_residual_image_global_ownership_9725.py').read_text(encoding='utf-8'))
write('prepare_original_symmetric_residual_global_ownership_9755.py',t)
t=rename((p/'compare_projective_residual_image_9725b.py').read_text(encoding='utf-8'))
t=t.replace('len(certs)==2','len(certs)==4').replace('==28','==30').replace("==939","==126")
start=t.index("sharedPath=p/")
end=t.index("ok=(result[",start)
t=t[:start]+"result['verifiedSharedGenerated']={}\nresult['unexplainedProductionNames']=result['productionNamesNotInScratch']\n"+t[end:]
t=t.replace('All 28 mathematical source bodies','All 30 mathematical source bodies')
write('compare_original_symmetric_residual_9755.py',t)
names=['SourceOriginalSymmetricDeclarations2354','SourceOriginalSymmetricAdjointDeclarations2366','SourceOriginalTwistedKernelDeclarations2377','SourceOriginalSymmetricJointDeclarations2383']
write('source-original-symmetric-residual-scratch-ownership-9755.json',json.dumps(names,indent=2)+'\n')

semantic_pairs=[
 ('SourceOriginalSymmetricScratchSemantic2360','SourceOriginalSymmetricProductionSemantic2360',95),
 ('SourceOriginalSymmetricAdjointScratchSemantic2375','SourceOriginalSymmetricAdjointProductionSemantic2375',17),
 ('SourceOriginalTwistedKernelScratchSemantic2379','SourceOriginalTwistedKernelProductionSemantic2379',48),
 ('SourceOriginalSymmetricJointScratchSemantic2385','SourceOriginalSymmetricJointProductionSemantic2385',18),
]
t=(p/'compare_projective_semantics_9725d.py').read_text(encoding='utf-8')
t=t.replace('def read(name):','def read(name,count):').replace('==1149','==count')
start=t.index("scratch=read(");end=t.index('missing=',start)
t=t[:start]+'''scratch={}; production={}
for left,right,count in '''+repr(semantic_pairs)+''':
 a=read(left,count);b=read(right,count)
 assert not set(a)&set(scratch) and not set(b)&set(production)
 scratch.update(a);production.update(b)
assert len(scratch)==len(production)==178
'''+t[end:]
t=t.replace('1149','178').replace('source-projective-semantic','source-original-symmetric-semantic').replace('9725','9755')
write('compare_original_symmetric_semantics_9755.py',t)

t=rename((p/'record_source_projective_residual_image_9725b.py').read_text(encoding='utf-8'))
t=t.replace("== 939","== 126").replace('== 1149','== 178').replace('== 28','== 30')
t=t.replace('"incrementModules": 28','"incrementModules": 30').replace('"linterScopes": 28','"linterScopes": 30').replace('"scratchExhaustiveTheorems": 939','"scratchExhaustiveTheorems": 126')
t=t.replace('== 2\n','== 4\n').replace('== 28319','== 28356')
t=t.replace('SOURCE PROJECTIVE RESIDUAL IMAGE AUDIT PASS','SOURCE ORIGINAL SYMMETRIC RESIDUAL AUDIT PASS')
t=t.replace('SOURCE PROJECTIVE (?:LINEAR|FINITE) VALUE AUDIT PASS:', 'SOURCE ORIGINAL (?:SYMMETRIC|SYMMETRIC ADJOINT|TWISTED KERNEL|SYMMETRIC JOINT) VALUE AUDIT PASS:')
t=t.replace('9,725','9,755').replace('original projective residual image and finite linear bounds','original symmetric residual and cohomology inputs')
t=t.replace('Two declaration-value audits verify 81 required dependency checks.', 'Four declaration-value audits verify 258 required dependency checks; a separate final-original-consumer audit verifies 26 more.')
t=t.replace('Dubon Projective Residual Image Assessment 2026-11-17.md','Dubon Original Symmetric Residual Assessment 2026-11-17.md')
t=t.replace('One additional Mathlib-generated congruence theorem is checked with identical type/value hashes in both consumer environments and is separately accounted for in the focused import order. No unaccounted theorem is missing.', 'Every focused theorem is accounted for; no unexplained additional or missing theorem is accepted. Independently normalized declaration types and values are checked across all four source scopes.')
needle='    receipt = {"proofDependencyAudits": deps,'
extra='''    extra = p / 'SourceOriginalResidueConsumerProductionAudit9755.log'
    assert extra.with_suffix('.exit').read_text().strip() == '0'
    extraText = extra.read_text(encoding='utf-16')
    assert 'all 26 required proof dependencies' in extraText and not re.search(bad,extraText)
    extraReceipt = dict(log=str(extra),sha256=sha(extra),sourceSha256=sha(extra.with_suffix('.lean')),requiredProofValueEdges=26)
'''
assert needle in t;t=t.replace(needle,extra+needle).replace('"proofDependencyAudits": deps,','"proofDependencyAudits": deps, "separateOriginalConsumerAudit": extraReceipt,')
write('record_source_original_symmetric_residual_9755.py',t)

t=rename((p/'archive_projective_residual_image_canonical_9725b.py').read_text(encoding='utf-8'))
t=t.replace('projective-residual-image-20261117-2326','original-symmetric-residual-20261117-2388')
start=t.index('extra=[');end=t.index('for f in sorted',start)
t=t[:start]+"extra=[]\n"+t[end:]
t=t.replace('archive_projective_residual_image_canonical_', 'archive_original_symmetric_residual_canonical_')
t=t.replace('Canonical PASS of the original projective residual image and finite linear bounds and its integral/residual realization, exact fixed-local Hecke data and global cyclotomic determinant.', 'Canonical PASS of symmetric spanning, absolute irreducibility, trace-zero adjoint vanishing and arithmetic twisted-cohomology detection for the same original residual representation, retaining its integral origin and all arithmetic data and the explicit small-image alternative.')
write('archive_original_symmetric_residual_canonical_9755.py',t)

# Execute one stage at a time; every log is new, retained and checked before
# moving on. The existing foundation and paper BATs remain unchanged.
t=r'''$ErrorActionPreference='Stop'
$taskScratch='E:\Lean\.tmp\dubon83'
$taskRepo='E:\Lean\Riemann Zeta'
$taskPaper=Join-Path $taskRepo '9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026'
$taskExtension=Join-Path $taskPaper 'Extension'
$env:ELAN_HOME='C:\Users\Naraphim\.elan'
Remove-Item Env:LEAN_PATH -ErrorAction SilentlyContinue
Set-Location -LiteralPath $taskExtension
function Invoke-TaskLean([string]$taskName) {
  $taskBase=Join-Path $taskScratch $taskName
  if(Test-Path -LiteralPath "$taskBase.log"){throw "Existing evidence: $taskName"}
  & 'C:\Users\Naraphim\.elan\bin\lake.exe' env lean -DautoImplicit=false "$taskBase.lean" *> "$taskBase.log"
  $taskExit=$LASTEXITCODE
  $taskExit | Out-File -LiteralPath "$taskBase.exit" -Encoding ascii
  if($taskExit -ne 0){Get-Content -LiteralPath "$taskBase.log" -Tail 15;throw "Failed: $taskName"}
  if(Select-String -LiteralPath "$taskBase.log" -Pattern '(^|\s)(warning:|error(?:\(|:)|PANIC\b)|Try this:|sorryAx|Found [1-9]'){throw "Diagnostics: $taskName"}
  Write-Output "PASS: $taskName"
}
$taskBuild=Join-Path $taskScratch 'source-original-symmetric-residual-production-build-9755'
if(Test-Path -LiteralPath "$taskBuild.log"){throw 'Existing aggregate evidence'}
& 'C:\Users\Naraphim\.elan\bin\lake.exe' build Dubon2026 *> "$taskBuild.log"
$taskExit=$LASTEXITCODE
$taskExit | Out-File -LiteralPath "$taskBuild.exit" -Encoding ascii
if($taskExit -ne 0){Get-Content -LiteralPath "$taskBuild.log" -Tail 20;exit $taskExit}
if(Select-String -LiteralPath "$taskBuild.log" -Pattern '(^|\s)(warning:|error(?:\(|:)|PANIC\b)|Try this:|sorryAx'){throw 'Aggregate diagnostics'}
Write-Output 'PASS: aggregate'
Invoke-TaskLean 'SourceOriginalSymmetricResidualProductionAudit9755'
foreach($taskName in (Get-Content -LiteralPath (Join-Path $taskScratch 'source-original-symmetric-residual-9755-production-audits.json') -Raw | ConvertFrom-Json)){Invoke-TaskLean $taskName}
Invoke-TaskLean 'SourceOriginalResidueConsumerProductionAudit9755'
python (Join-Path $taskScratch 'prepare_original_symmetric_residual_production_ownership_9755.py')
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
Invoke-TaskLean 'SourceOriginalSymmetricResidualOwnership9755'
python (Join-Path $taskScratch 'compare_original_symmetric_residual_9755.py')
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
'''
for _,name,_ in semantic_pairs:t+="Invoke-TaskLean '"+name+"'\n"
t+=r'''python (Join-Path $taskScratch 'compare_original_symmetric_semantics_9755.py')
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
python (Join-Path $taskScratch 'record_source_original_symmetric_residual_9755.py') --focused
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
Set-Location -LiteralPath $taskRepo
$taskRoot=Join-Path $taskScratch 'root-verification-9755-console'
if(Test-Path -LiteralPath "$taskRoot.log"){throw 'Existing foundation evidence'}
$ErrorActionPreference='Continue'
cmd /c run_lake_build.bat --no-pause *> "$taskRoot.log"
$taskExit=$LASTEXITCODE
$ErrorActionPreference='Stop'
$taskExit | Out-File -LiteralPath "$taskRoot.exit" -Encoding ascii
Get-Content -LiteralPath "$taskRoot.log" -Tail 14
if($taskExit -ne 0){exit $taskExit}
Set-Location -LiteralPath $taskPaper
$taskPaperLog=Join-Path $taskScratch 'paper-verification-9755-console'
if(Test-Path -LiteralPath "$taskPaperLog.log"){throw 'Existing paper evidence'}
$ErrorActionPreference='Continue'
cmd /c run_dubon_build.bat --no-pause *> "$taskPaperLog.log"
$taskExit=$LASTEXITCODE
$ErrorActionPreference='Stop'
$taskExit | Out-File -LiteralPath "$taskPaperLog.exit" -Encoding ascii
Get-Content -LiteralPath "$taskPaperLog.log" -Tail 16
if($taskExit -ne 0){exit $taskExit}
Set-Location -LiteralPath $taskExtension
python (Join-Path $taskScratch 'prepare_original_symmetric_residual_global_ownership_9755.py')
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
Invoke-TaskLean 'SourceOriginalSymmetricResidualGlobalOwnership9755'
python (Join-Path $taskScratch 'record_source_original_symmetric_residual_9755.py') --canonical
exit $LASTEXITCODE
'''
write('verify_original_symmetric_residual_9755.ps1',t)
print('Prepared strict production verification, ownership and four-scope semantic reconciliation; no production mutation.')
