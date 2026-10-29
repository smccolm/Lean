$ErrorActionPreference='Stop'
foreach($name in @('SourceEvenWeightFrickeUniformPreflight1651','SourceEvenWeightFrickeUniformValuePreflight1651')){
 & powershell -NoProfile -ExecutionPolicy Bypass -File "E:\Lean\.tmp\dubon83\audit_$($name)_1651.ps1"
 if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
}
