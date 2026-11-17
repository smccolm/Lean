$ErrorActionPreference='Stop'
$taskScratch='E:\Lean\.tmp\dubon83'
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceOriginalTorusPrimeLocalProperties'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceOriginalTorusPrimePredicates'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceOriginalTorusDetectionPredicate'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceOriginalTorusDetectionAssembly'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceOriginalTorusPrimeDimensions'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceOriginalTorusPrimeAssembly'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceOriginalArithmeticTorusPrimes'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceOriginalArithmeticTorusPrimeProperty'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceGammaOneOriginalTorusPrimes'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceOriginalTorusClassPredicates'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceOriginalTorusCocycleClass'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceOriginalTorusClassPrimes'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceOriginalTorusFamilyProperty'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceOriginalTorusDetectingFamily'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceOriginalArithmeticTorusFamilies'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceGammaOneOriginalTorusFamilies'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_dickson_audit_2285.ps1') -Name 'SourceOriginalTorusAudit2'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_dickson_audit_2285.ps1') -Name 'SourceOriginalTorusDependencyAudit2'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_dickson_audit_2285.ps1') -Name 'SourceOriginalTorusDeclarations2480'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_dickson_audit_2285.ps1') -Name 'SourceOriginalTorusScratchSemantic2481'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
