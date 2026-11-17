$ErrorActionPreference='Stop'
$taskScratch='E:\Lean\.tmp\dubon83'
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceOriginalTorusDetectionAssembly2454c'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceOriginalTorusPrimeAssembly2449e'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceOriginalArithmeticTorusPrimes2450b'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceOriginalArithmeticTorusPrimeProperty2451b'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceGammaOneOriginalTorusPrimes2452b'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceOriginalArithmeticTorusFamilies2466b'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
& (Join-Path $taskScratch 'run_scratch_module_1433.ps1') -Name 'SourceGammaOneOriginalTorusFamilies2467b'
if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
