$ErrorActionPreference='Stop'
$taskScratch='E:\Lean\.tmp\dubon83'
foreach($taskName in @('SourceOriginalSymmetricAdjoint','SourceGammaOneSymmetricAdjointVanishing')) {
 powershell -NoProfile -ExecutionPolicy Bypass -File (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name $taskName
 if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
}
foreach($taskName in @('SourceOriginalSymmetricAdjointAudit1','SourceOriginalSymmetricAdjointDependencyAudit1','SourceOriginalSymmetricAdjointDeclarations2366')) {
 powershell -NoProfile -ExecutionPolicy Bypass -File (Join-Path $taskScratch 'run_dickson_audit_2285.ps1') -Name $taskName
 if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
}