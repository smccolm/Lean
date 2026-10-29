$ErrorActionPreference='Stop'
$env:ELAN_HOME='C:\Users\Naraphim\.elan'
$env:LEAN_PATH='E:\Lean\.tmp\dubon83'
Set-Location -LiteralPath 'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension'
$names=@('SourceGammaOneGaloisDiamondPolynomial1436c','SourceGammaOneDiamondQuotientPolynomial1439e','SourceGammaOneDiamondQuotientHecke1440e')
foreach($n in $names){
 $base="E:\Lean\.tmp\dubon83\$n"
 if(Test-Path -LiteralPath "$base.log"){throw "Evidence exists: $base"}
 & 'C:\Users\Naraphim\.elan\bin\lake.exe' env lean -DautoImplicit=false -R 'E:\Lean\.tmp\dubon83' -o "$base.olean" "$base.lean" *> "$base.log"
 $rc=$LASTEXITCODE
 $rc | Out-File -LiteralPath "$base.exit" -Encoding ascii
 if($rc -ne 0 -or (Get-Item -LiteralPath "$base.log").Length -ne 0){Get-Content -LiteralPath "$base.log" -Encoding Unicode;exit 1}
 Write-Output "PASS: $n"
}
