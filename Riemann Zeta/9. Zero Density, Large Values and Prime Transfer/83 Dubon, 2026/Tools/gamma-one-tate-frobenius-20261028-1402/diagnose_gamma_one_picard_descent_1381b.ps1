$ErrorActionPreference='Stop'
$taskScratch='E:\Lean\.tmp\dubon83'
$env:ELAN_HOME='C:\Users\Naraphim\.elan'
$env:LEAN_PATH=$taskScratch
Set-Location -LiteralPath 'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension'
$taskLog=Join-Path $taskScratch 'SourceGammaOneHeckePicardDescent1381b-diagnostics'
if(Test-Path -LiteralPath "$taskLog.log"){throw 'Diagnostic evidence already exists'}
& 'C:\Users\Naraphim\.elan\bin\lake.exe' env lean -DautoImplicit=false -Ddiagnostics=true (Join-Path $taskScratch 'SourceGammaOneHeckePicardDescent1381b.lean') *> "$taskLog.log"
$taskCode=$LASTEXITCODE
$taskCode | Set-Content -LiteralPath "$taskLog.exit"
Get-Content -LiteralPath "$taskLog.log" -Tail 45
exit $taskCode
