$ErrorActionPreference='Stop'
$taskScratch='E:\Lean\.tmp\dubon83'
foreach($taskName in @('SourceFiniteSubfieldIrreducible','SourceSubfieldSymmetricAbsolute','SourceFiniteLinearSymmetric','SourceGammaOneAbsoluteSymmetricResidual')) {
 & powershell -NoProfile -ExecutionPolicy Bypass -File (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name $taskName
 if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
}
foreach($taskName in @('SourceSubfieldSymmetricAudit1','SourceSubfieldSymmetricDependencyAudit1','SourceSubfieldSymmetricDeclarations2334')) {
 & powershell -NoProfile -ExecutionPolicy Bypass -File (Join-Path $taskScratch 'run_dickson_audit_2285.ps1') -Name $taskName
 if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
}
