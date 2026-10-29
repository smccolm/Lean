$ErrorActionPreference='Stop'
$taskScratch='E:\Lean\.tmp\dubon83'
if((Get-Content -LiteralPath (Join-Path $taskScratch 'SourceGammaOneGaussValuation1269b.exit') -Raw).Trim() -ne '0'){throw 'Valuation did not pass'}
foreach($taskScript in @('compile_SourceGammaOneGaussResidueHom_1270b.ps1','compile_SourceGammaOneGaussResidueKernel_1271a.ps1','compile_SourceGammaOneGaussConstants_1272a.ps1')){
 & powershell -NoProfile -ExecutionPolicy Bypass -File (Join-Path $taskScratch $taskScript)
 if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
 Write-Output "PASS $taskScript"
}
exit 0
