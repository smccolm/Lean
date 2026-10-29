$ErrorActionPreference='Stop'
foreach($name in @('SourceGammaOneDegreePreflight1715','SourceGammaOneDegreeValuePreflight1715')){
 & powershell -NoProfile -ExecutionPolicy Bypass -File "E:\Lean\.tmp\dubon83\audit_$($name)_1715.ps1"
 if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
}
