param([Parameter(Mandatory=$true)][string]$Name)
$ErrorActionPreference='Stop'
if($Name -notmatch '^[A-Za-z0-9_]+$'){throw 'Invalid name'}
$env:ELAN_HOME='C:\Users\Naraphim\.elan'
$env:LEAN_PATH='E:\Lean\.tmp\dubon83'
Set-Location -LiteralPath 'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension'
$base="E:\Lean\.tmp\dubon83\$Name"
if(Test-Path -LiteralPath "$base.log"){throw 'Evidence already exists'}
& 'C:\Users\Naraphim\.elan\bin\lake.exe' env lean -DautoImplicit=false "$base.lean" *> "$base.log"
$rc=$LASTEXITCODE
$rc | Out-File -LiteralPath "$base.exit" -Encoding ascii
Get-Content -LiteralPath "$base.log" -Encoding Unicode | Select-Object -Last 50
if($rc -ne 0){exit $rc}
if(Select-String -LiteralPath "$base.log" -Pattern '(^|\s)(warning:|error(?:\(|:)|PANIC\b)|Try this:|sorryAx|Found [1-9]'){exit 1}
