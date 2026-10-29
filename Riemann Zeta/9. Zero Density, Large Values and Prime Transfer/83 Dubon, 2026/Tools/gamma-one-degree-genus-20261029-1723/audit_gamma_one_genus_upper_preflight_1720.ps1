$ErrorActionPreference='Stop'
foreach($name in @('SourceGammaOneGenusUpperPreflight1720','SourceGammaOneGenusUpperValuePreflight1720')){
 & powershell -NoProfile -ExecutionPolicy Bypass -File "E:\Lean\.tmp\dubon83\audit_$($name)_1720.ps1"
 if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
}
