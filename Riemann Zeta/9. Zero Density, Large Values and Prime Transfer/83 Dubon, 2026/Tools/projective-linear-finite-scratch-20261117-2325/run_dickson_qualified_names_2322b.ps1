$ErrorActionPreference='Stop'
$taskScratch='E:\Lean\.tmp\dubon83'
$taskProbe=Join-Path $taskScratch 'dickson-qualified-name-probe-2322'
$env:LEAN_PATH=$taskProbe+';'+$env:LEAN_PATH
$taskName='SourceDicksonPGLBasic'
$taskLog=Join-Path $taskProbe ($taskName+'-2322b.log')
if(Test-Path -LiteralPath $taskLog){throw 'Evidence exists'}
& lean.exe -DautoImplicit=false -R $taskProbe -o (Join-Path $taskProbe "Dubon2026\$taskName.olean") (Join-Path $taskProbe "Dubon2026\$taskName.lean") *> $taskLog
$taskCode=$LASTEXITCODE
$taskCode | Out-File -LiteralPath (Join-Path $taskProbe ($taskName+'-2322b.exit')) -Encoding ascii
if($taskCode -ne 0 -or (Get-Item -LiteralPath $taskLog).Length -ne 0){Get-Content -LiteralPath $taskLog -Encoding Unicode | Select-Object -Last 25;exit 1}
Write-Output 'PASS: qualified SourceDicksonPGLBasic'
$taskBase=Join-Path $taskScratch 'SourceDicksonQualifiedNames2322'
if(Test-Path -LiteralPath "$taskBase.log"){throw 'Evidence exists'}
& lean.exe -DautoImplicit=false "$taskBase.lean" *> "$taskBase.log"
$taskCode=$LASTEXITCODE
$taskCode | Out-File -LiteralPath "$taskBase.exit" -Encoding ascii
Get-Content -LiteralPath "$taskBase.log" -Encoding Unicode | Select-Object -Last 10
exit $taskCode
