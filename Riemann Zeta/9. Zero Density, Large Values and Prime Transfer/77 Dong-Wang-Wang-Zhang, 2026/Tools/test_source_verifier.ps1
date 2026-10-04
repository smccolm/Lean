Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'
$fixtureRoot = Join-Path $PSScriptRoot ('..\logs\source-verifier-tests-' + (Get-Date -Format 'yyyyMMdd-HHmmss-fff'))
New-Item -ItemType Directory -Path $fixtureRoot -Force | Out-Null
$utf8 = New-Object System.Text.UTF8Encoding($false)
$bytes = $utf8.GetBytes('generated source-verifier fixture')
$sha = [Security.Cryptography.SHA256]::Create()
try { $hash = ([BitConverter]::ToString($sha.ComputeHash($bytes))).Replace('-', '').ToLowerInvariant() }
finally { $sha.Dispose() }
$verifier = Join-Path $PSScriptRoot 'verify_sources.ps1'
$cases = @('valid', 'changed', 'missing', 'extra', 'duplicate', 'nonlocal', 'empty', 'malformed')
foreach ($case in $cases) {
    $caseRoot = Join-Path $fixtureRoot $case
    New-Item -ItemType Directory -Path $caseRoot | Out-Null
    if ($case -ne 'missing') { [IO.File]::WriteAllBytes((Join-Path $caseRoot 'a.bin'), $bytes) }
    $ledger = "$hash  a.bin`n"
    switch ($case) {
        'changed' { [IO.File]::WriteAllBytes((Join-Path $caseRoot 'a.bin'), $utf8.GetBytes('changed fixture')) }
        'extra' { [IO.File]::WriteAllBytes((Join-Path $caseRoot 'extra.bin'), $bytes) }
        'duplicate' { $ledger += $ledger }
        'nonlocal' { $ledger = "$hash  ../a.bin`n" }
        'empty' { $ledger = '' }
        'malformed' { $ledger = 'not-a-sha256-ledger' }
    }
    [IO.File]::WriteAllText((Join-Path $caseRoot 'SHA256SUMS.txt'), $ledger, $utf8)
    $accepted = $true
    $message = ''
    try { & $verifier -SourceRoot $caseRoot | Out-Null }
    catch { $accepted = $false; $message = $_.Exception.Message }
    if ($accepted -ne ($case -eq 'valid')) { throw "Unexpected verifier result for $case : $message" }
    Write-Output "TEST PASS: $case (accepted=$accepted) $message"
}
Write-Output "TOOLING TESTS PASS: $($cases.Count); no Lean proof tested. Generated fixtures retained at $fixtureRoot"
