$ErrorActionPreference='Stop'
$taskScratch='E:\Lean\.tmp\dubon83'
$taskExtension='E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension'
$env:ELAN_HOME='C:\Users\Naraphim\.elan'
Remove-Item Env:LEAN_PATH -ErrorAction SilentlyContinue
Set-Location -LiteralPath $taskExtension
$taskBuild=Join-Path $taskScratch 'source-primitive-finite-h1-realization-production-build-8235'
if(Test-Path -LiteralPath "$taskBuild.log"){throw 'Aggregate evidence already exists'}
& 'C:\Users\Naraphim\.elan\bin\lake.exe' build Dubon2026 *> "$taskBuild.log"
$taskCode=$LASTEXITCODE
$taskCode | Set-Content "$taskBuild.exit"
if($taskCode -ne 0){Get-Content -LiteralPath "$taskBuild.log" -Tail 25;exit $taskCode}
if(Select-String -LiteralPath "$taskBuild.log" -Pattern '(^|\s)(warning:|error(?:\(|:)|PANIC\b)|Try this:'){throw 'Aggregate diagnostics'}
foreach($taskHelper in @('prepare_primitive_finite_h1_realization_production_ownership_8235.py','prepare_primitive_finite_h1_realization_scratch_ownership_8235.py')){
 python (Join-Path $taskScratch $taskHelper)
 if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
}
$taskAudits=[System.Collections.Generic.List[string]]::new()
$taskAudits.Add('SourcePrimitiveFiniteH1RealizationProductionAudit8235')
$taskDependencyNames=Get-Content -LiteralPath (Join-Path $taskScratch 'source-primitive-finite-h1-realization-8235-production-audits.json') -Raw | ConvertFrom-Json
foreach($taskName in $taskDependencyNames){$taskAudits.Add([string]$taskName)}
$taskAudits.Add('SourcePrimitiveFiniteH1RealizationOwnership8235')
foreach($taskName in $taskAudits){
 $taskBase=Join-Path $taskScratch $taskName
 if(Test-Path -LiteralPath "$taskBase.log"){throw 'Audit evidence already exists'}
 & 'C:\Users\Naraphim\.elan\bin\lake.exe' env lean -DautoImplicit=false "$taskBase.lean" *> "$taskBase.log"
 $taskCode=$LASTEXITCODE
 $taskCode | Set-Content "$taskBase.exit"
 if($taskCode -ne 0){Get-Content -LiteralPath "$taskBase.log" -Tail 25;exit $taskCode}
 if(Select-String -LiteralPath "$taskBase.log" -Pattern '(^|\s)(warning:|error(?:\(|:)|PANIC\b)|Try this:|sorryAx|Found [1-9]'){throw 'Audit diagnostics'}
 Write-Output "PASS: $taskName"
}
$env:LEAN_PATH=$taskScratch
$taskScratchNames=Get-Content -LiteralPath (Join-Path $taskScratch 'source-primitive-finite-h1-realization-scratch-ownership-8235.json') -Raw | ConvertFrom-Json
foreach($taskName in $taskScratchNames){
 $taskBase=Join-Path $taskScratch ([string]$taskName)
 if(Test-Path -LiteralPath "$taskBase.log"){throw 'Scratch audit evidence already exists'}
 & 'C:\Users\Naraphim\.elan\bin\lake.exe' env lean -DautoImplicit=false "$taskBase.lean" *> "$taskBase.log"
 $taskCode=$LASTEXITCODE
 $taskCode | Set-Content "$taskBase.exit"
 if($taskCode -ne 0){Get-Content -LiteralPath "$taskBase.log" -Tail 25;exit $taskCode}
 if(Select-String -LiteralPath "$taskBase.log" -Pattern '(^|\s)(warning:|error(?:\(|:)|PANIC\b)|Try this:|sorryAx|Found [1-9]'){throw 'Scratch audit diagnostics'}
 Write-Output "PASS: $taskName"
}
Remove-Item Env:LEAN_PATH -ErrorAction SilentlyContinue
& powershell -NoProfile -ExecutionPolicy Bypass -File (Join-Path $taskScratch 'verify_primitive_finite_h1_realization_8235.ps1')
exit $LASTEXITCODE
