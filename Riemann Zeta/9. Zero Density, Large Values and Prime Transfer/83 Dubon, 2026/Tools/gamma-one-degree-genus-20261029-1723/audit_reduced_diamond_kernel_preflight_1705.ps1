$ErrorActionPreference='Stop'
foreach($name in @('SourceReducedDiamondKernelPreflight1705','SourceReducedDiamondKernelValuePreflight1705')){
 & powershell -NoProfile -ExecutionPolicy Bypass -File "E:\Lean\.tmp\dubon83\audit_$($name)_1705.ps1"
 if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
}
