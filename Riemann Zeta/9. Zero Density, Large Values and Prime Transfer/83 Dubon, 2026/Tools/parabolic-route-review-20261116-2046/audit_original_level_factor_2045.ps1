$ErrorActionPreference='Stop'
$env:ELAN_HOME='C:\Users\Naraphim\.elan'
$env:LEAN_PATH='E:\Lean\.tmp\dubon83'
Set-Location -LiteralPath 'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension'
$base='E:\Lean\.tmp\dubon83\SourceGammaOneOriginalLevelFactorAudit2045'
if(Test-Path -LiteralPath "$base.log"){throw 'Evidence exists'}
& 'C:\Users\Naraphim\.elan\bin\lake.exe' env lean -DautoImplicit=false "$base.lean" *> "$base.log"
$rc=$LASTEXITCODE
$rc | Set-Content -LiteralPath "$base.exit"
if($rc -ne 0){Get-Content -LiteralPath "$base.log" -Encoding Unicode;exit $rc}
if(Select-String -LiteralPath "$base.log" -Pattern 'warning:|error(?:\(|:)|PANIC|Try this:|sorryAx|Found [1-9]'){throw 'Audit diagnostics'}
Write-Output 'PASS SourceGammaOneOriginalLevelFactorAudit2045'
