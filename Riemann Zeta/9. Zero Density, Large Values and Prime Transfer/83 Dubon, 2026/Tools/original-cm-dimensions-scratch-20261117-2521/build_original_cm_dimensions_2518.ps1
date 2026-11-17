$ErrorActionPreference='Stop'
$taskScratch='E:\Lean\.tmp\dubon83'
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceOriginalCMAdjointVanishing'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceOriginalCMCotangent'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceOriginalCMCotangentFormula'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceOriginalIntegralCMDimensionData'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceOriginalSupportBottomBounds'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceOriginalIntegralCMDimensionField'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceOriginalIntegralCMDimensionProperty'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceOriginalIntegralCMDimensionAssembly'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceGammaOneOriginalCMDimensions'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_dickson_audit_2285.ps1') -Name 'SourceOriginalCMDimensionsAudit1'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_dickson_audit_2285.ps1') -Name 'SourceOriginalCMDimensionsDependencyAudit1'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_dickson_audit_2285.ps1') -Name 'SourceOriginalCMDimensionsDeclarations2518'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_dickson_audit_2285.ps1') -Name 'SourceOriginalCMDimensionsScratchSemantic2519'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
