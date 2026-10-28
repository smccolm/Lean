$ErrorActionPreference='Stop'
$env:ELAN_HOME='C:\Users\Naraphim\.elan'
$env:LEAN_PATH='E:\Lean\.tmp\dubon83'
Set-Location -LiteralPath 'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension'
if((Get-Content -LiteralPath 'E:\Lean\.tmp\dubon83\SourceParabolicCosetPotentials937c.exit').Trim() -ne '0'){throw 'Coset compile failed'}
$rows=@(
 @('SourceModularPeriodCorners','938e'),
 @('SourceWeightTwoCosetPeriods','939c'),
 @('SourceParabolicWindingIntegralPeriods','940b'),
 @('SourceGammaOneDivisorWindingIntegralPeriod','941c')
)
foreach($row in $rows){
 $m=$row[0];$v=$row[1];$b="E:\Lean\.tmp\dubon83\$m";$e="$b$v"
 if(Test-Path -LiteralPath "$e.log"){throw "Evidence exists $e"}
 & 'C:\Users\Naraphim\.elan\bin\lake.exe' env lean -DautoImplicit=false --root 'E:\Lean\.tmp\dubon83' -o "$b.olean" "$b.lean" *> "$e.log"
 $rc=$LASTEXITCODE
 $rc | Set-Content -LiteralPath "$e.exit" -Encoding ascii
 if($rc -ne 0 -or (Get-Item -LiteralPath "$e.log").Length -ne 0){Get-Content -LiteralPath "$e.log";exit 1}
 Write-Output "PASS $m"
}
& powershell.exe -NoProfile -ExecutionPolicy Bypass -File 'E:\Lean\.tmp\dubon83\audit_original_winding_integral_period_943b.ps1'
exit $LASTEXITCODE
