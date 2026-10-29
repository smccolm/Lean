$ErrorActionPreference='Stop'
foreach($name in @('SourceEvenWeightFrickeUniformPreflight1652','SourceEvenWeightFrickeUniformValuePreflight1652')){
 & powershell -NoProfile -ExecutionPolicy Bypass -File "E:\Lean\.tmp\dubon83\audit_$($name)_1652.ps1"
 if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
}
