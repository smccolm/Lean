$ErrorActionPreference='Stop'
foreach($n in @('SourceFrickeLevelIntegralRing1630b','SourceFrickeDenominatorUniformization1634b','SourceEvenWeightFrickeTrace1635b')){
 & powershell -NoProfile -ExecutionPolicy Bypass -File 'E:\Lean\.tmp\dubon83un_scratch_module_1433.ps1' -Name $n
 if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
}
