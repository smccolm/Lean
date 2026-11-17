$ErrorActionPreference='Stop'
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
Invoke-TaskLean 'SourceOriginalSymmetricProductionSemantic2360'
Invoke-TaskLean 'SourceOriginalSymmetricAdjointProductionSemantic2375'
Invoke-TaskLean 'SourceOriginalTwistedKernelProductionSemantic2379'
Invoke-TaskLean 'SourceOriginalSymmetricJointProductionSemantic2385'
python (Join-Path $taskScratch 'compare_original_symmetric_semantics_9755.py')
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
