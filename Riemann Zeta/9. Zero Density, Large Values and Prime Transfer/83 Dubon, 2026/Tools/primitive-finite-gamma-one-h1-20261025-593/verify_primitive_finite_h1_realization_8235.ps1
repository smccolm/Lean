$ErrorActionPreference='Stop'
$taskScratch='E:\Lean\.tmp\dubon83'
$taskRepo='E:\Lean\Riemann Zeta'
$taskPaper=Join-Path $taskRepo '9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026'
$taskExtension=Join-Path $taskPaper 'Extension'
$env:ELAN_HOME='C:\Users\Naraphim\.elan'
Remove-Item Env:LEAN_PATH -ErrorAction SilentlyContinue
Set-Location -LiteralPath $taskExtension
# Scratch ownership was independently executed before promotion; preserve its logs.
$taskScratchNames=Get-Content -LiteralPath (Join-Path $taskScratch 'source-primitive-finite-h1-realization-scratch-ownership-8235.json') -Raw | ConvertFrom-Json
foreach($taskName in $taskScratchNames){
  $taskSource=Join-Path $taskScratch $taskName
  if((Get-Content -LiteralPath "$taskSource.exit" -Raw).Trim() -ne '0'){throw 'Scratch ownership did not pass'}
  if(Select-String -LiteralPath "$taskSource.log" -Pattern '(^|\s)(warning:|error(?:\(|:)|PANIC\b)|Try this:|sorryAx|Found [1-9]'){throw 'Scratch ownership diagnostics'}
}
python (Join-Path $taskScratch 'compare_primitive_finite_h1_realization_ownership_8235.py')
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
python (Join-Path $taskScratch 'record_source_primitive_finite_h1_realization_8235.py') --focused
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
Set-Location -LiteralPath $taskRepo
$taskRoot=Join-Path $taskScratch 'root-verification-8235-console'
if(Test-Path -LiteralPath "$taskRoot.log"){throw 'Foundation evidence already exists'}
cmd /c run_lake_build.bat --no-pause *> "$taskRoot.log"
$taskExit=$LASTEXITCODE
$taskExit | Set-Content -LiteralPath "$taskRoot.exit"
Get-Content -LiteralPath "$taskRoot.log" -Encoding Unicode | Select-Object -Last 14
if($taskExit -ne 0){exit $taskExit}
Set-Location -LiteralPath $taskPaper
$taskPaperLog=Join-Path $taskScratch 'paper-verification-8235-console'
if(Test-Path -LiteralPath "$taskPaperLog.log"){throw 'Paper evidence already exists'}
cmd /c run_dubon_build.bat --no-pause *> "$taskPaperLog.log"
$taskExit=$LASTEXITCODE
$taskExit | Set-Content -LiteralPath "$taskPaperLog.exit"
Get-Content -LiteralPath "$taskPaperLog.log" -Encoding Unicode | Select-Object -Last 16
if($taskExit -ne 0){exit $taskExit}
Set-Location -LiteralPath $taskExtension
python (Join-Path $taskScratch 'prepare_primitive_finite_h1_realization_global_ownership_8235.py')
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
$taskGlobal=Join-Path $taskScratch 'SourcePrimitiveFiniteH1RealizationGlobalOwnership8235'
if(Test-Path -LiteralPath "$taskGlobal.log"){throw 'Global ownership evidence already exists'}
& 'C:\Users\Naraphim\.elan\bin\lake.exe' env lean -DautoImplicit=false "$taskGlobal.lean" *> "$taskGlobal.log"
$taskExit=$LASTEXITCODE
$taskExit | Set-Content -LiteralPath "$taskGlobal.exit"
if($taskExit -ne 0){Get-Content -LiteralPath "$taskGlobal.log";exit $taskExit}
if(Select-String -LiteralPath "$taskGlobal.log" -Pattern '(^|\s)(warning:|error(?:\(|:)|PANIC\b)|Try this:|sorryAx|Found [1-9]'){exit 1}
python (Join-Path $taskScratch 'record_source_primitive_finite_h1_realization_8235.py') --canonical
exit $LASTEXITCODE
