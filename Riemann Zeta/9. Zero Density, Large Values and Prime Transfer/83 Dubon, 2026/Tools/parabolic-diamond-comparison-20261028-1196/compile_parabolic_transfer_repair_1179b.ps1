$ErrorActionPreference='Stop'
$env:ELAN_HOME='C:\Users\Naraphim\.elan'
$env:LEAN_PATH='E:\Lean\.tmp\dubon83'
Set-Location -LiteralPath 'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension'
$scratch='E:\Lean\.tmp\dubon83'
foreach($row in @(@('SourceGammaOneParabolicTateKernel','1177d'),@('SourceGammaOneParabolicTransferCriterion','1179b'),@('SourceGammaOneParabolicCharacterTransfer','1178c'))){
 $m=$row[0];$a=$row[1];$ev=Join-Path $scratch ($m+$a)
 if(Test-Path -LiteralPath "$ev.log"){throw 'Evidence already exists'}
 & 'C:\Users\Naraphim\.elan\bin\lake.exe' env lean -DautoImplicit=false --root $scratch -o "$scratch\$m.olean" "$scratch\$m.lean" *> "$ev.log"
 $rc=$LASTEXITCODE
 $rc | Set-Content -LiteralPath "$ev.exit"
 if($rc -ne 0 -or (Get-Item -LiteralPath "$ev.log").Length -ne 0){Get-Content -LiteralPath "$ev.log";exit 1}
 Write-Output "PASS $m$a"
}
