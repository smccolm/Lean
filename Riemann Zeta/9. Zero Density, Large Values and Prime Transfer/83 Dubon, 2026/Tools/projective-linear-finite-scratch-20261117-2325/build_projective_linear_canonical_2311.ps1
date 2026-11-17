$ErrorActionPreference='Stop'
$env:ELAN_HOME='C:\Users\Naraphim\.elan'
$env:LEAN_PATH='E:\Lean\.tmp\dubon83'
$taskScratch='E:\Lean\.tmp\dubon83'
Set-Location -LiteralPath 'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension'
$taskConfig=Get-Content -LiteralPath (Join-Path $taskScratch 'source-projective-linear-preparation-2311.json') -Raw | ConvertFrom-Json
foreach($taskRow in $taskConfig.files){
  $taskSource=Join-Path $taskScratch ($taskRow.module + '.lean')
  if((Get-FileHash -LiteralPath $taskSource -Algorithm SHA256).Hash -ne $taskRow.canonicalSha256){throw 'Proof body hash changed'}
}
foreach($taskRow in ($taskConfig.files | Select-Object -Skip 15)){
  $taskName=$taskRow.module
  $taskBase=Join-Path $taskScratch ($taskName + '-2311')
  if(Test-Path -LiteralPath "$taskBase.log"){throw 'Evidence exists'}
  & 'C:\Users\Naraphim\.elan\bin\lake.exe' env lean -DautoImplicit=false -R $taskScratch -o (Join-Path $taskScratch "$taskName.olean") (Join-Path $taskScratch "$taskName.lean") *> "$taskBase.log"
  $taskExit=$LASTEXITCODE
  $taskExit | Out-File -LiteralPath "$taskBase.exit" -Encoding ascii
  if($taskExit -ne 0 -or (Get-Item -LiteralPath "$taskBase.log").Length -ne 0){Get-Content -LiteralPath "$taskBase.log" -Encoding Unicode | Select-Object -Last 35;exit 1}
  Write-Output "PASS: $taskName"
}
& powershell -NoProfile -ExecutionPolicy Bypass -File (Join-Path $taskScratch 'run_dickson_audit_2285.ps1') -Name SourceProjectiveLinearDeclarations2311
exit $LASTEXITCODE
