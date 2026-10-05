Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'
$paperRoot = Split-Path -Parent $PSScriptRoot
$logRoot = Join-Path $paperRoot 'logs'
New-Item -ItemType Directory -Path $logRoot -Force | Out-Null
$logPath = Join-Path $logRoot ('dhiman-kadiri-quesada-herrera-scaffold-' + (Get-Date -Format 'yyyyMMdd-HHmmss-fff') + '.log')
$resultCode = 1
$transcriptStarted = $false
try {
    Start-Transcript -Path $logPath | Out-Null
    $transcriptStarted = $true
    Write-Output 'DKKH project 78: planning scaffold verification, not a Lean proof run.'
    & (Join-Path $PSScriptRoot 'verify_sources.ps1')
    & python -X utf8 (Join-Path $PSScriptRoot 'verify_scaffold.py')
    if ($LASTEXITCODE -ne 0) { throw "Scaffold validator failed with exit $LASTEXITCODE" }
    & (Join-Path $PSScriptRoot 'test_source_verifier.ps1')
    Write-Output 'SCAFFOLD PASS - LEAN CONVERSION NOT STARTED. Proof gates: 0/20.'
    $resultCode = 0
} catch {
    Write-Output ('SCAFFOLD FAILED: ' + $_.Exception.Message)
} finally {
    Write-Output "Log: $logPath"
    if ($transcriptStarted) { Stop-Transcript | Out-Null }
}
exit $resultCode
