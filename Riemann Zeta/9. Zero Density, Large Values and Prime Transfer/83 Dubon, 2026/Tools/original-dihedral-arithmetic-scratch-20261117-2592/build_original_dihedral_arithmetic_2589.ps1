$ErrorActionPreference='Stop'
$taskScratch='E:\Lean\.tmp\dubon83'
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceProjectiveInvolutionTrace'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceOriginalProjectiveInvolutionTrace'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceDihedralReflectionSign'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceOriginalDihedralCharacter'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceOriginalDihedralContinuity'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceOriginalDihedralArithmetic'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceOriginalNonCMDihedralInputsProperty'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceGammaOneOriginalDihedralInputs'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_dickson_audit_2285.ps1') -Name 'SourceOriginalDihedralArithmeticAudit1'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_dickson_audit_2285.ps1') -Name 'SourceOriginalDihedralArithmeticDependencyAudit1'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_dickson_audit_2285.ps1') -Name 'SourceOriginalDihedralArithmeticDeclarations2589'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_dickson_audit_2285.ps1') -Name 'SourceOriginalDihedralArithmeticScratchSemantic2590'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
