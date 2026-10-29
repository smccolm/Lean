$ErrorActionPreference='Stop'
$taskScratch='E:\Lean\.tmp\dubon83'
$env:ELAN_HOME='C:\Users\Naraphim\.elan'
$env:LEAN_PATH=$taskScratch
Set-Location -LiteralPath 'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension'
foreach($taskName in @('SourceGammaOneTwistedContinuity1420a')){
 $taskBase=Join-Path $taskScratch $taskName
 if(Test-Path -LiteralPath "$taskBase.log"){throw 'Evidence already exists'}
 & 'C:\Users\Naraphim\.elan\bin\lake.exe' env lean -DautoImplicit=false -R $taskScratch -o "$taskBase.olean" "$taskBase.lean" *> "$taskBase.log"
 $taskCode=$LASTEXITCODE
 $taskCode | Set-Content -LiteralPath "$taskBase.exit"
 if($taskCode -ne 0){Get-Content -LiteralPath "$taskBase.log";exit $taskCode}
 if((Get-Item -LiteralPath "$taskBase.log").Length -ne 0){Get-Content -LiteralPath "$taskBase.log";exit 1}
 Write-Output "PASS $taskName"
}
