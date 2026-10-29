$ErrorActionPreference='Stop'
$env:ELAN_HOME='C:\Users\Naraphim\.elan'
$env:LEAN_PATH='E:\Lean\.tmp\dubon83'
Set-Location -LiteralPath 'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension'
$names=@('SourceTateOriginalJCoordinate','SourceMarkedChartCoordinateEmbedding','SourceMarkedChartVariableInvariants','SourceMarkedChartEqualJTransfer','SourceMarkedChartInvariantSeparation','SourceMarkedChartFieldDescent','SourceMarkedChartTorsionDescent','SourceMarkedChartEmbeddingBound','SourceMarkedChartResidueDegree','SourceMarkedChartDescendedPoint','SourceMarkedChartOriginalConstruction','SourceMarkedChartStabilizerInclusion','SourceMarkedChartOriginalStabilizer')
foreach($n in $names){
 $base="E:\Lean\.tmp\dubon83\$n-1914"
 if(Test-Path -LiteralPath "$base.log"){throw "Evidence exists: $n"}
 & 'C:\Users\Naraphim\.elan\bin\lake.exe' env lean -DautoImplicit=false -R 'E:\Lean\.tmp\dubon83' -o "E:\Lean\.tmp\dubon83\$n.olean" "E:\Lean\.tmp\dubon83\$n.lean" *> "$base.log"
 $rc=$LASTEXITCODE
 $rc | Out-File -LiteralPath "$base.exit" -Encoding ascii
 if($rc -ne 0 -or (Get-Item -LiteralPath "$base.log").Length -ne 0){Get-Content -LiteralPath "$base.log" -Encoding Unicode;exit 1}
 Write-Output "PASS: $n"
}
& powershell -NoProfile -ExecutionPolicy Bypass -File 'E:\Lean\.tmp\dubon83\audit_marked_chart_construction_1914.ps1'
exit $LASTEXITCODE
