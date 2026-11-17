$ErrorActionPreference='Stop'
$env:ELAN_HOME='C:\Users\Naraphim\.elan'
$env:LEAN_PATH='E:\Lean\.tmp\dubon83'
$taskScratch='E:\Lean\.tmp\dubon83'
Set-Location -LiteralPath 'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension'
$taskConfig=Get-Content -LiteralPath (Join-Path $taskScratch 'original-unramified-rank-two-audit-config-2235.json') -Raw | ConvertFrom-Json
foreach($taskName in $taskConfig.modules){
  $taskBase=Join-Path $taskScratch "$taskName-2235"
  if(Test-Path -LiteralPath "$taskBase.log"){throw 'Evidence exists'}
  & 'C:\Users\Naraphim\.elan\bin\lake.exe' env lean -DautoImplicit=false -R $taskScratch -o (Join-Path $taskScratch "$taskName.olean") (Join-Path $taskScratch "$taskName.lean") *> "$taskBase.log"
  $taskExit=$LASTEXITCODE
  $taskExit | Out-File -LiteralPath "$taskBase.exit" -Encoding ascii
  if($taskExit -ne 0 -or (Get-Item -LiteralPath "$taskBase.log").Length -ne 0){Get-Content -LiteralPath "$taskBase.log" -Encoding Unicode;exit 1}
  Write-Output "PASS: $taskName"
}
foreach($taskName in @('SourceOriginalUnramifiedRankTwoAudit1','SourceOriginalUnramifiedRankTwoDependencyAudit1','SourceOriginalUnramifiedRankTwoScratchOwnership2235')){
  $taskBase=Join-Path $taskScratch $taskName
  if(Test-Path -LiteralPath "$taskBase.log"){throw 'Evidence exists'}
  & 'C:\Users\Naraphim\.elan\bin\lake.exe' env lean -DautoImplicit=false "$taskBase.lean" *> "$taskBase.log"
  $taskExit=$LASTEXITCODE
  $taskExit | Out-File -LiteralPath "$taskBase.exit" -Encoding ascii
  if($taskExit -ne 0 -or (Select-String -LiteralPath "$taskBase.log" -Pattern '(^|\s)(warning:|error(?:\(|:)|PANIC\b)|Try this:|sorryAx|Found [1-9]')){Get-Content -LiteralPath "$taskBase.log" -Encoding Unicode;exit 1}
  Write-Output "PASS: $taskName"
}
