$ErrorActionPreference='Stop'
$taskScratch='E:\Lean\.tmp\dubon83'
if((Get-Content -LiteralPath (Join-Path $taskScratch 'SourceLaurentCoefficientProjection1206c.exit') -Raw).Trim() -ne '0'){throw 'Prerequisite failed'}
if((Get-Item -LiteralPath (Join-Path $taskScratch 'SourceLaurentCoefficientProjection1206c.log')).Length -ne 0){throw 'Prerequisite diagnostics'}
$env:ELAN_HOME='C:\Users\Naraphim\.elan'
$env:LEAN_PATH=$taskScratch
Set-Location -LiteralPath 'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension'
$taskBase=Join-Path $taskScratch 'SourceLaurentFieldIntersection1207b'
if(Test-Path -LiteralPath "$taskBase.log"){throw 'Evidence exists'}
& 'C:\Users\Naraphim\.elan\bin\lake.exe' env lean -DautoImplicit=false --root $taskScratch -o (Join-Path $taskScratch 'SourceLaurentFieldIntersection.olean') (Join-Path $taskScratch 'SourceLaurentFieldIntersection.lean') *> "$taskBase.log"
$taskExit=$LASTEXITCODE
$taskExit | Set-Content -LiteralPath "$taskBase.exit"
Get-Content -LiteralPath "$taskBase.log"
exit $taskExit

