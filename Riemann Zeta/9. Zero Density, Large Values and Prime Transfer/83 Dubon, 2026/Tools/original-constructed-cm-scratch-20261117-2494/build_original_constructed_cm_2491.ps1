$ErrorActionPreference='Stop'
$taskScratch='E:\Lean\.tmp\dubon83'
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceOriginalCMKernelConsequences'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceOriginalRationalBottomRestriction'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceOriginalRationalCMProperty'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceGammaOneOriginalCMConsequences'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceOriginalRationalBottomOdd'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceOriginalRationalCMPolarized'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceOriginalRationalCMPolarizationProperty'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceGammaOneOriginalCMPolarized'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceOriginalCMQuadraticField'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceOriginalSupportCyclotomic'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceOriginalSupportResidual'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceOriginalConstructedCMProperty'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceOriginalConstructedCMAssembly'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceGammaOneOriginalConstructedCM'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_dickson_audit_2285.ps1') -Name 'SourceOriginalConstructedCMAudit1'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_dickson_audit_2285.ps1') -Name 'SourceOriginalConstructedCMDependencyAudit1'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_dickson_audit_2285.ps1') -Name 'SourceOriginalConstructedCMDeclarations2491'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_dickson_audit_2285.ps1') -Name 'SourceOriginalConstructedCMScratchSemantic2492'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
