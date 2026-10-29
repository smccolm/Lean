$ErrorActionPreference='Stop'
$taskScratch='E:\Lean\.tmp\dubon83'
$env:ELAN_HOME='C:\Users\Naraphim\.elan'
$env:LEAN_PATH=$taskScratch
Set-Location -LiteralPath 'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension'
$taskBase=Join-Path $taskScratch 'SourceGammaOneResidueCoordinateFinite1277b'
if(Test-Path -LiteralPath "$taskBase.log"){throw 'Evidence exists'}
& 'C:\Users\Naraphim\.elan\bin\lake.exe' env lean -DautoImplicit=false --root $taskScratch -o (Join-Path $taskScratch 'SourceGammaOneResidueCoordinateFinite.olean') (Join-Path $taskScratch 'SourceGammaOneResidueCoordinateFinite.lean') *> "$taskBase.log"
$taskExit=$LASTEXITCODE
$taskExit | Set-Content -LiteralPath "$taskBase.exit"
Get-Content -LiteralPath "$taskBase.log"
exit $taskExit
