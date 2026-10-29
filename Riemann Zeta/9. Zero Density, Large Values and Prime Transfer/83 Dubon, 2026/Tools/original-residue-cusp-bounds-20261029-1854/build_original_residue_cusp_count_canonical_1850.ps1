$ErrorActionPreference='Stop'
$env:ELAN_HOME='C:\Users\Naraphim\.elan'
$env:LEAN_PATH='E:\Lean\.tmp\dubon83'
Set-Location -LiteralPath 'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension'
$names=@('SourceOriginalResidueImageCuspCount')
foreach($n in $names){
 $base="E:\Lean\.tmp\dubon83\$n"
 $ev=$base+'-1850'
 if(Test-Path -LiteralPath "$ev.log"){throw "Evidence exists: $ev"}
 & 'C:\Users\Naraphim\.elan\bin\lake.exe' env lean -DautoImplicit=false -R 'E:\Lean\.tmp\dubon83' -o "$base.olean" "$base.lean" *> "$ev.log"
 $rc=$LASTEXITCODE
 $rc | Out-File -LiteralPath "$ev.exit" -Encoding ascii
 if($rc -ne 0 -or (Get-Item -LiteralPath "$ev.log").Length -ne 0 -or (Select-String -LiteralPath "$ev.log" -Pattern 'warning:|error(?:\(|:)|PANIC|Try this:|sorryAx|Found [1-9]')){
  Get-Content -LiteralPath "$ev.log" -Encoding Unicode -Tail 30
  exit 1
 }
 Write-Output "PASS: $n"
}

& powershell -NoProfile -ExecutionPolicy Bypass -File 'E:\Lean\.tmp\dubon83\audit_original_residue_cusp_count_1850.ps1'
exit $LASTEXITCODE
