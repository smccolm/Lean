$ErrorActionPreference='Stop'
$taskScratch='E:\Lean\.tmp\dubon83'
$taskConfig=Get-Content -LiteralPath (Join-Path $taskScratch 'source-original-twisted-kernel-audit-config-2377.json') -Raw | ConvertFrom-Json
foreach($taskName in $taskConfig.modules) {
 powershell -NoProfile -ExecutionPolicy Bypass -File (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name $taskName
 if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
}
foreach($taskName in @('SourceOriginalTwistedKernelAudit1','SourceOriginalTwistedKernelDependencyAudit1','SourceOriginalTwistedKernelDeclarations2377')) {
 powershell -NoProfile -ExecutionPolicy Bypass -File (Join-Path $taskScratch 'run_dickson_audit_2285.ps1') -Name $taskName
 if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
}