$ErrorActionPreference='Stop'
$taskScratch='E:\Lean\.tmp\dubon83'
$taskExtension='E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension'
$env:ELAN_HOME='C:\Users\Naraphim\.elan'
Remove-Item Env:LEAN_PATH -ErrorAction SilentlyContinue
Set-Location -LiteralPath $taskExtension
$taskBuild=Join-Path $taskScratch 'source-toric-marked-point-production-build-9450'
if(Test-Path -LiteralPath "$taskBuild.log"){throw 'Aggregate evidence already exists'}
& 'C:\Users\Naraphim\.elan\bin\lake.exe' build Dubon2026 *> "$taskBuild.log"
$taskCode=$LASTEXITCODE
$taskCode | Set-Content "$taskBuild.exit"
if($taskCode -ne 0){Get-Content -LiteralPath "$taskBuild.log" -Tail 25;exit $taskCode}
if(Select-String -LiteralPath "$taskBuild.log" -Pattern '(^|\s)(warning:|error(?:\(|:)|PANIC\b)|Try this:'){throw 'Aggregate diagnostics'}
foreach($taskHelper in @('prepare_toric_marked_point_production_ownership_9450.py')){
 python (Join-Path $taskScratch $taskHelper)
 if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
}
$taskAudits=[System.Collections.Generic.List[string]]::new()
$taskAudits.Add('SourceToricMarkedPointProductionAudit9450')
$taskDependencyNames=Get-Content -LiteralPath (Join-Path $taskScratch 'source-toric-marked-point-9450-production-audits.json') -Raw | ConvertFrom-Json
foreach($taskName in $taskDependencyNames){$taskAudits.Add([string]$taskName)}
$taskAudits.Add('SourceToricMarkedPointOwnership9450')
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
# Reuse the already passed immutable scratch ownership logs; verification checks them.
Remove-Item Env:LEAN_PATH -ErrorAction SilentlyContinue
& powershell -NoProfile -ExecutionPolicy Bypass -File (Join-Path $taskScratch 'verify_toric_marked_point_9450.ps1')
exit $LASTEXITCODE
