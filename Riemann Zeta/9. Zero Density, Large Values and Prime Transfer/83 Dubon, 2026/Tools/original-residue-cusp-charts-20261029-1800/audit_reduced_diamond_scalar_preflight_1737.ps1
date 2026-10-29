$ErrorActionPreference='Stop'
foreach($name in @('SourceReducedDiamondScalarPreflight1737','SourceReducedDiamondScalarValuePreflight1737')){
 & powershell -NoProfile -ExecutionPolicy Bypass -File "E:\Lean\.tmp\dubon83\audit_$($name)_1737.ps1"
 if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
}
