$ErrorActionPreference='Stop'
$taskScratch='E:\Lean\.tmp\dubon83'
foreach($taskName in @('SourceFiniteLinearOriginalConsequences','SourceGammaOneSymmetricResidualCohomology')) {
 powershell -NoProfile -ExecutionPolicy Bypass -File (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name $taskName
 if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
}
foreach($taskName in @('SourceOriginalSymmetricJointAudit1','SourceOriginalSymmetricJointDependencyAudit1','SourceOriginalSymmetricJointDeclarations2383')) {
 powershell -NoProfile -ExecutionPolicy Bypass -File (Join-Path $taskScratch 'run_dickson_audit_2285.ps1') -Name $taskName
 if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
}