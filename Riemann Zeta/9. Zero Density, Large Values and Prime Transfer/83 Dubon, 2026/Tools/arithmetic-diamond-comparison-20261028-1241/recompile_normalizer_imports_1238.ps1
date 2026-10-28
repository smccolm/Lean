$ErrorActionPreference='Stop'
$taskScratch='E:\Lean\.tmp\dubon83'
$env:ELAN_HOME='C:\Users\Naraphim\.elan'
$env:LEAN_PATH=$taskScratch
Set-Location -LiteralPath 'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension'
foreach($row in @(@('SourceGammaOneDiamondCoefficient','1235b'),@('SourceGammaOneDiamondRestriction','1236b'),@('SourceGammaOneDiamondCoefficientMatrix','1237c'))){
 $taskBase=Join-Path $taskScratch ($row[0]+$row[1])
 if(Test-Path -LiteralPath "$taskBase.log"){throw 'Evidence exists'}
 & 'C:\Users\Naraphim\.elan\bin\lake.exe' env lean -DautoImplicit=false --root $taskScratch -o (Join-Path $taskScratch ($row[0]+'.olean')) (Join-Path $taskScratch ($row[0]+'.lean')) *> "$taskBase.log"
 $taskExit=$LASTEXITCODE
 $taskExit | Set-Content -LiteralPath "$taskBase.exit"
 if($taskExit -ne 0 -or (Get-Item -LiteralPath "$taskBase.log").Length -ne 0){Get-Content -LiteralPath "$taskBase.log";exit 1}
 Write-Output ('PASS '+$row[0])
}
