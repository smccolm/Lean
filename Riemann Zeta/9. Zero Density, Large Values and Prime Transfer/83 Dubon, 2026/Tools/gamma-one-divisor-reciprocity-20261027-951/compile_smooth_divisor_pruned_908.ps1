$ErrorActionPreference='Stop'
$env:ELAN_HOME='C:\Users\Naraphim\.elan'
$env:LEAN_PATH='E:\Lean\.tmp\dubon83'
Set-Location -LiteralPath 'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension'
$mods=@('SourceModularSmoothProjectiveRepresentatives','SourceSmoothModularGeometry','SourceSmoothProjectiveOrbitSum','SourceSmoothDivisorOrbitData','SourceSmoothModularLogDerivative','SourceSmoothDivisorProduct','SourceSmoothDivisorLocalProduct','SourceSmoothDivisorLocalOrders','SourceSmoothDivisorInvarianceCusps','SourceSmoothDivisorLogDerivative','SourceSmoothInvariantComparison','SourceGammaOneSmoothDivisorComparison')
foreach($m in $mods) {
 $src="E:\Lean\.tmp\dubon83\$m.lean"
 $out="E:\Lean\.tmp\dubon83\$m.olean"
 $log="E:\Lean\.tmp\dubon83\${m}908a.log"
 $ex="E:\Lean\.tmp\dubon83\${m}908a.exit"
 if((Test-Path -LiteralPath $log) -or (Test-Path -LiteralPath $ex)) {throw "Evidence exists: $m"}
 & 'C:\Users\Naraphim\.elan\bin\lake.exe' env lean -DautoImplicit=false --root 'E:\Lean\.tmp\dubon83' -o $out $src *> $log
 $rc=$LASTEXITCODE
 $rc | Out-File -LiteralPath $ex -Encoding ascii
 if($rc -ne 0 -or (Get-Item -LiteralPath $log).Length -ne 0) {Get-Content -LiteralPath $log -Encoding Unicode;throw "Compile failed: $m"}
 Write-Output "PASS $m"
}
