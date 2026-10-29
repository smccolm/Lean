$ErrorActionPreference='Stop'
foreach($name in @('SourceReducedDiamondKernelPreflight1701','SourceReducedDiamondKernelValuePreflight1701')){
 & powershell -NoProfile -ExecutionPolicy Bypass -File "E:\Lean\.tmp\dubon83\audit_$($name)_1701.ps1"
 if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
}
