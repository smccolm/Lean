$ErrorActionPreference='Stop'
$taskScratch='E:\Lean\.tmp\dubon83'
foreach($taskName in @('SourceGammaOneDiamondFieldRatios1197c','SourceGammaOneFieldCuspGerm1198a')){
 if((Get-Content -LiteralPath (Join-Path $taskScratch "$taskName.exit") -Raw).Trim() -ne '0'){throw 'Prerequisite failed'}
 if((Get-Item -LiteralPath (Join-Path $taskScratch "$taskName.log")).Length -ne 0){throw 'Prerequisite diagnostics'}
}
$env:ELAN_HOME='C:\Users\Naraphim\.elan'
$env:LEAN_PATH=$taskScratch
Set-Location -LiteralPath 'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension'
$taskBase=Join-Path $taskScratch 'SourceGammaOneDiamondFieldHom1199a'
if(Test-Path -LiteralPath "$taskBase.log"){throw 'Evidence exists'}
& 'C:\Users\Naraphim\.elan\bin\lake.exe' env lean -DautoImplicit=false --root $taskScratch -o (Join-Path $taskScratch 'SourceGammaOneDiamondFieldHom.olean') (Join-Path $taskScratch 'SourceGammaOneDiamondFieldHom.lean') *> "$taskBase.log"
$taskExit=$LASTEXITCODE
$taskExit | Set-Content -LiteralPath "$taskBase.exit"
Get-Content -LiteralPath "$taskBase.log"
exit $taskExit
