Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'
$paperRoot = Split-Path -Parent $PSScriptRoot
$logRoot = Join-Path $paperRoot 'logs'
New-Item -ItemType Directory -Path $logRoot -Force | Out-Null
$logPath = Join-Path $logRoot ('dubon-build-' + (Get-Date -Format 'yyyyMMdd-HHmmss-fff') + '.log')
$resultCode = 1
$transcriptStarted = $false

function Invoke-LeanGate {
    param([string]$Label, [string[]]$Arguments)
    Write-Output "STAGE: $Label"
    Push-Location -LiteralPath (Join-Path $paperRoot 'Extension')
    try {
        $savedPreference = $ErrorActionPreference
        try {
            $ErrorActionPreference = 'Continue'
            $output = @(& $lakeCommand.Source @Arguments 2>&1)
            $nativeExit = $LASTEXITCODE
        } finally { $ErrorActionPreference = $savedPreference }
        $output | ForEach-Object { Write-Output "$_" }
        if (@($output | Where-Object {
            $_ -is [System.Management.Automation.ErrorRecord] -and
            $_.FullyQualifiedErrorId -notin @('NativeCommandError', 'NativeCommandErrorMessage')
        }).Count -ne 0) { throw "$Label invocation failed" }
        if ($nativeExit -ne 0) { throw "$Label exited $nativeExit" }
        if (@($output | Where-Object {
            "$_" -match '(^|\s)(warning:|error:)|Try this:|Found [1-9][0-9]* errors'
        }).Count -ne 0) { throw "$Label emitted a prohibited Lean diagnostic" }
        Write-Output "PASS: $Label; exit 0; zero Lean diagnostics"
    } finally { Pop-Location }
}

try {
    Start-Transcript -Path $logPath | Out-Null
    $transcriptStarted = $true
    $config = Get-Content -LiteralPath (Join-Path $PSScriptRoot 'scaffold.json') -Raw -Encoding UTF8 | ConvertFrom-Json
    if ($config.mode -eq 'project-complete') {
        Write-Output 'DUB project 83: SOURCE CONTRACT VERIFICATION'
    } else {
        Write-Output 'DUB project 83: ACTIVE DEVELOPMENT VERIFICATION'
    }
    & (Join-Path $PSScriptRoot 'verify_sources.ps1')
    & python -X utf8 (Join-Path $PSScriptRoot 'verify_scaffold.py')
    if ($LASTEXITCODE -ne 0) { throw "Project validator failed with exit $LASTEXITCODE" }
    & (Join-Path $PSScriptRoot 'test_source_verifier.ps1')
    & python -X utf8 (Join-Path $PSScriptRoot 'inspect_source_archive.py')
    if ($LASTEXITCODE -ne 0) { throw 'Archive inspection failed' }
    & python -X utf8 (Join-Path $PSScriptRoot 'test_scaffold.py')
    if ($LASTEXITCODE -ne 0) { throw 'Inventory regression tests failed' }
    $lakeCommand = Get-Command lake -ErrorAction Stop
    if ([string]::IsNullOrWhiteSpace($env:ELAN_HOME)) {
        $elanCandidate = Split-Path -Parent (Split-Path -Parent $lakeCommand.Source)
        if (-not (Test-Path -LiteralPath (Join-Path $elanCandidate 'toolchains'))) { throw 'Cannot infer ELAN_HOME.' }
        $env:ELAN_HOME = $elanCandidate
    }
    $moduleRoot = 'Dubon2026'
    $buildArguments = @('build', $moduleRoot) + @($config.verificationModules | ForEach-Object { "$moduleRoot.$_" })
    Invoke-LeanGate 'complete package and retained verification builds' $buildArguments
    foreach ($module in $config.verificationModules) {
        Invoke-LeanGate $module @('env', 'lean', ($moduleRoot + '/' + $module.Replace('.', '/') + '.lean'))
    }
    if ($config.mode -eq 'project-complete') {
        Write-Output 'PROOF PASS - ALL ACCEPTED SOURCE CONTRACTS VERIFIED; 20/20 GATES'
    } else {
        Write-Output "DEVELOPMENT PASS - IMPLEMENTED SCOPE VERIFIED; $($config.proofGatesComplete)/20 GATES COMPLETE; PAPER INCOMPLETE"
    }
    $resultCode = 0
} catch {
    Write-Output ('VERIFICATION FAIL: ' + $_.Exception.Message)
} finally {
    Write-Output "Log: $logPath"
    if ($transcriptStarted) { Stop-Transcript | Out-Null }
}
exit $resultCode
