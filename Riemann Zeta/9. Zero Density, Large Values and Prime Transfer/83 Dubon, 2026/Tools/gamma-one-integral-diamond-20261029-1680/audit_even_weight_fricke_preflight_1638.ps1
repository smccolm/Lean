$ErrorActionPreference='Stop'
foreach($name in @('SourceEvenWeightFrickeTracePreflight1638','SourceEvenWeightFrickeTraceValuePreflight1638')){
 & powershell -NoProfile -ExecutionPolicy Bypass -File "E:\Lean\.tmp\dubon83\audit_$($name)_1638.ps1"
 if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
}
