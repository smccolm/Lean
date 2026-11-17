$ErrorActionPreference='Stop'
$taskScratch='E:\Lean\.tmp\dubon83'
$taskProbe=Join-Path $taskScratch 'dickson-qualified-name-probe-2322'
$env:ELAN_HOME='C:\Users\Naraphim\.elan'
$env:LEAN_PATH=$taskProbe
Set-Location -LiteralPath 'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension'
foreach($taskName in @('SourceDicksonObjects','SourceDicksonPGLBasic')){
  $taskSource=Join-Path $taskProbe ("Dubon2026\$taskName.lean")
  $taskLog=Join-Path $taskProbe ($taskName+'.log')
  if(Test-Path -LiteralPath $taskLog){throw 'Evidence exists'}
  & 'C:\Users\Naraphim\.elan\bin\lake.exe' env lean -DautoImplicit=false -R $taskProbe -o (Join-Path $taskProbe "Dubon2026\$taskName.olean") $taskSource *> $taskLog
  $taskCode=$LASTEXITCODE
  $taskCode | Out-File -LiteralPath (Join-Path $taskProbe ($taskName+'.exit')) -Encoding ascii
  if($taskCode -ne 0 -or (Get-Item -LiteralPath $taskLog).Length -ne 0){Get-Content -LiteralPath $taskLog -Encoding Unicode | Select-Object -Last 25;exit 1}
  Write-Output "PASS: qualified $taskName"
}
$taskBase=Join-Path $taskScratch 'SourceDicksonQualifiedNames2322'
if(Test-Path -LiteralPath "$taskBase.log"){throw 'Evidence exists'}
& 'C:\Users\Naraphim\.elan\bin\lake.exe' env lean -DautoImplicit=false "$taskBase.lean" *> "$taskBase.log"
$taskCode=$LASTEXITCODE
$taskCode | Out-File -LiteralPath "$taskBase.exit" -Encoding ascii
Get-Content -LiteralPath "$taskBase.log" -Encoding Unicode | Select-Object -Last 10
exit $taskCode
