$ErrorActionPreference='Stop'
foreach($name in @('SourceReducedDiamondActionPreflight1694','SourceReducedDiamondActionValuePreflight1694')){
 & powershell -NoProfile -ExecutionPolicy Bypass -File "E:\Lean\.tmp\dubon83\audit_$($name)_1694.ps1"
 if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
}
