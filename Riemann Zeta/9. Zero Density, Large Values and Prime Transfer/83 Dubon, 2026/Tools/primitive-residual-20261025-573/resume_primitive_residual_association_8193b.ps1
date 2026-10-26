$ErrorActionPreference='Stop'
$taskScratch='E:\Lean\.tmp\dubon83'
$taskExtension='E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension'
$env:ELAN_HOME='C:\Users\Naraphim\.elan'
Remove-Item Env:LEAN_PATH -ErrorAction SilentlyContinue
Set-Location -LiteralPath $taskExtension
foreach($taskPassed in @('source-primitive-residual-association-production-build-8193','SourcePrimitiveResidualAssociationProductionAudit8193')){
 $taskPassedBase=Join-Path $taskScratch $taskPassed
 if((Get-Content -LiteralPath "$taskPassedBase.exit" -Raw).Trim() -ne '0'){throw 'Required preceding stage failed'}
 if(Select-String -LiteralPath "$taskPassedBase.log" -Pattern '(^|\s)(warning:|error(?:\(|:)|PANIC\b)|Try this:|sorryAx|Found [1-9]'){throw 'Preceding diagnostics'}
}
$taskAudits=Get-Content -LiteralPath (Join-Path $taskScratch 'source-primitive-residual-association-8193-production-audits.json') -Raw | ConvertFrom-Json
$taskAudits+= 'SourcePrimitiveResidualAssociationOwnership8193'
foreach($taskName in $taskAudits){
 $taskBase=Join-Path $taskScratch ([string]$taskName)
 if(Test-Path -LiteralPath "$taskBase.log"){throw 'Audit evidence already exists'}
 & 'C:\Users\Naraphim\.elan\bin\lake.exe' env lean -DautoImplicit=false "$taskBase.lean" *> "$taskBase.log"
 $taskCode=$LASTEXITCODE
 $taskCode | Set-Content "$taskBase.exit"
 if($taskCode -ne 0){Get-Content -LiteralPath "$taskBase.log" -Tail 30;exit $taskCode}
 if(Select-String -LiteralPath "$taskBase.log" -Pattern '(^|\s)(warning:|error(?:\(|:)|PANIC\b)|Try this:|sorryAx|Found [1-9]'){exit 1}
 Write-Output "PASS: $taskName"
}
$env:LEAN_PATH=$taskScratch
$taskScratchAudits=Get-Content -LiteralPath (Join-Path $taskScratch 'source-primitive-residual-association-scratch-ownership-8193.json') -Raw | ConvertFrom-Json
foreach($taskName in $taskScratchAudits){
 $taskBase=Join-Path $taskScratch ([string]$taskName)
 if(Test-Path -LiteralPath "$taskBase.log"){throw 'Scratch ownership evidence already exists'}
 & 'C:\Users\Naraphim\.elan\bin\lake.exe' env lean -DautoImplicit=false "$taskBase.lean" *> "$taskBase.log"
 $taskCode=$LASTEXITCODE
 $taskCode | Set-Content "$taskBase.exit"
 if($taskCode -ne 0){Get-Content -LiteralPath "$taskBase.log" -Tail 30;exit $taskCode}
 if(Select-String -LiteralPath "$taskBase.log" -Pattern '(^|\s)(warning:|error(?:\(|:)|PANIC\b)|Try this:|sorryAx|Found [1-9]'){exit 1}
 Write-Output "PASS: $taskName"
}
Remove-Item Env:LEAN_PATH -ErrorAction SilentlyContinue
& powershell -NoProfile -ExecutionPolicy Bypass -File (Join-Path $taskScratch 'verify_primitive_residual_association_8193b.ps1')
exit $LASTEXITCODE
