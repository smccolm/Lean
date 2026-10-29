$ErrorActionPreference='Stop'
foreach($name in @('SourceIntegralDiamondFieldPull1683d','SourceIntegralDiamondFieldRange1684b','SourceIntegralDiamondFieldConstants1685c','SourceIntegralDiamondFieldOperations1686b','SourceIntegralDiamondFieldComposition1688c','SourceIntegralDiamondFieldIdentity1689b','SourceIntegralDiamondFieldAction1690b')){
 & powershell -NoProfile -ExecutionPolicy Bypass -File 'E:\Lean\.tmp\dubon83\run_scratch_module_1433.ps1' -Name $name
 if($LASTEXITCODE -ne 0){exit $LASTEXITCODE}
}
