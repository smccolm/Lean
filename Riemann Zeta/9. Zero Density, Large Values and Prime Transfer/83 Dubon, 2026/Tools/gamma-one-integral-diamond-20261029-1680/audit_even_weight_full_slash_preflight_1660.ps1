$ErrorActionPreference='Stop'
foreach($name in @('SourceEvenWeightFullSlashPreflight1660','SourceEvenWeightFullSlashValuePreflight1660')){
 & powershell -NoProfile -ExecutionPolicy Bypass -File "E:\Lean\.tmp\dubon83\audit_$($name)_1660.ps1"
 if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
}
