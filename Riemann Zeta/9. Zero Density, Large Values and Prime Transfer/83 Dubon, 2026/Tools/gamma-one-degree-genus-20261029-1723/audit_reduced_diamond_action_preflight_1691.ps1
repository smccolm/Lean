$ErrorActionPreference='Stop'
foreach($name in @('SourceReducedDiamondActionPreflight1691','SourceReducedDiamondActionValuePreflight1691')){
 & powershell -NoProfile -ExecutionPolicy Bypass -File "E:\Lean\.tmp\dubon83\audit_$($name)_1691.ps1"
 if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
}
