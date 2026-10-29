$ErrorActionPreference='Stop'
foreach($name in @('SourceEvenWeightIntegralDiamondPreflight1668','SourceEvenWeightIntegralDiamondValuePreflight1668')){
 & powershell -NoProfile -ExecutionPolicy Bypass -File "E:\Lean\.tmp\dubon83\audit_$($name)_1668.ps1"
 if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
}
