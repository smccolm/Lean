$ErrorActionPreference='Stop'
foreach($name in @('SourceReducedDiamondScalarPreflight1740','SourceReducedDiamondScalarValuePreflight1740')){
 & powershell -NoProfile -ExecutionPolicy Bypass -File "E:\Lean\.tmp\dubon83\audit_$($name)_1740.ps1"
 if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
}
