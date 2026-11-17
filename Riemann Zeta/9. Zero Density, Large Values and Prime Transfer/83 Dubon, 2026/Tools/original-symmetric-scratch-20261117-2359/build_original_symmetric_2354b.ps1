$ErrorActionPreference='Stop'
$taskScratch='E:\Lean\.tmp\dubon83'
$taskConfig=Get-Content -LiteralPath (Join-Path $taskScratch 'source-original-cyclotomic-symmetric-audit-config-2354.json') -Raw | ConvertFrom-Json
foreach($taskName in ($taskConfig.modules | Select-Object -Skip 9)) {
  powershell -NoProfile -ExecutionPolicy Bypass -File (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name $taskName
  if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
}
foreach($taskName in @('SourceOriginalSymmetricAudit1','SourceOriginalSymmetricDependencyAudit1','SourceOriginalSymmetricDeclarations2354')) {
  powershell -NoProfile -ExecutionPolicy Bypass -File (Join-Path $taskScratch 'run_dickson_audit_2285.ps1') -Name $taskName
  if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
}