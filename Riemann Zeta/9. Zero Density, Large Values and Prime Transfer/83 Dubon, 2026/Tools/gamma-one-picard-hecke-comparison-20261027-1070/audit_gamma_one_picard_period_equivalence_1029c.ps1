$ErrorActionPreference='Stop'
$env:ELAN_HOME='C:\Users\Naraphim\.elan'
$env:LEAN_PATH='E:\Lean\.tmp\dubon83'
Set-Location -LiteralPath 'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension'
$modules=@('SourceWeightTwoEvaluationFrame','SourceWeightTwoEndpointImage','SourceWeightTwoEndpointOpenImage','SourceWeightTwoJacobiInversion','SourceGammaOneJacobiInversion','SourceGammaOneAnalyticPicardPresentation','SourceGammaOnePicardPeriodKernel','SourceGammaOnePicardPeriodEquiv')
foreach($m in $modules){
 $f="E:\Lean\.tmp\dubon83\$m"
 $ev="$($f)1029c"
 if(Test-Path -LiteralPath "$ev.log"){throw "Evidence exists: $ev"}
 & 'C:\Users\Naraphim\.elan\bin\lake.exe' env lean -DautoImplicit=false --root 'E:\Lean\.tmp\dubon83' -o "$f.olean" "$f.lean" *> "$ev.log"
 $rc=$LASTEXITCODE
 $rc | Out-File -LiteralPath "$ev.exit" -Encoding ascii
 if($rc -ne 0 -or (Get-Item -LiteralPath "$ev.log").Length -ne 0){Get-Content -LiteralPath "$ev.log" -Encoding Unicode;exit 1}
 Write-Output "PASS $m"
}
$names=@('SourceGammaOnePicardPeriodEquivalenceAudit1c','SourceGammaOnePicardPeriodEquivalenceDependencyAudit1c','SourceGammaOnePicardPeriodEquivalenceScratchOwnership1029c')
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
python 'E:\Lean\.tmp\dubon83\record_source_gamma_one_picard_period_equivalence_1029c.py'
exit $LASTEXITCODE
