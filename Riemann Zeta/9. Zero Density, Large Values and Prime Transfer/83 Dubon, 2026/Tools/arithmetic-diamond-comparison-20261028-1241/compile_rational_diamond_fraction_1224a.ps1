$ErrorActionPreference='Stop'
$taskScratch='E:\Lean\.tmp\dubon83'
$env:ELAN_HOME='C:\Users\Naraphim\.elan'
$env:LEAN_PATH=$taskScratch
Set-Location -LiteralPath 'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension'
$taskBase=Join-Path $taskScratch 'SourceRationalDiamondFraction1224a'
if(Test-Path -LiteralPath "$taskBase.log"){throw 'Evidence exists'}
& 'C:\Users\Naraphim\.elan\bin\lake.exe' env lean -DautoImplicit=false --root $taskScratch -o (Join-Path $taskScratch 'SourceRationalDiamondFraction.olean') (Join-Path $taskScratch 'SourceRationalDiamondFraction.lean') *> "$taskBase.log"
$taskExit=$LASTEXITCODE
$taskExit | Set-Content -LiteralPath "$taskBase.exit"
Get-Content -LiteralPath "$taskBase.log"
exit $taskExit
