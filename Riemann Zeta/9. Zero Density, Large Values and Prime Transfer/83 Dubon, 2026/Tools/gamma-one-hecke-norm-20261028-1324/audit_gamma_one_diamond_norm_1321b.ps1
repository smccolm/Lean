$ErrorActionPreference='Stop'
$env:ELAN_HOME='C:\Users\Naraphim\.elan'
$env:LEAN_PATH='E:\Lean\.tmp\dubon83'
Set-Location -LiteralPath 'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension'
$names=@('SourceGammaOneDiamondNormAudit2','SourceGammaOneDiamondNormDependencyAudit2','SourceGammaOneDiamondNormScratchOwnership1321b')
foreach($n in $names){
 $base="E:\Lean\.tmp\dubon83\$n"
 if(Test-Path -LiteralPath "$base.log"){throw "Evidence exists: $n"}
 & 'C:\Users\Naraphim\.elan\bin\lake.exe' env lean -DautoImplicit=false "$base.lean" *> "$base.log"
 $rc=$LASTEXITCODE
 $rc | Out-File -LiteralPath "$base.exit" -Encoding ascii
 if($rc -ne 0 -or (Select-String -LiteralPath "$base.log" -Pattern 'warning:|error(?:\(|:)|PANIC|Try this:|sorryAx|Found [1-9]')){
  Get-Content -LiteralPath "$base.log" -Encoding Unicode -Tail 40;exit 1
 }
 Write-Output "PASS $n"
}
python 'E:\Lean\.tmp\dubon83\record_gamma_one_diamond_norm_1321b.py'
exit $LASTEXITCODE
