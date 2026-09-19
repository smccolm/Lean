[CmdletBinding()]
param()

$ErrorActionPreference = 'Stop'
$buildTranscriptActive = $false
$buildExitCode = 1
$buildLogPath = $null

function Assert-ProjectFile {
    param(
        [Parameter(Mandatory = $true)]
        [string] $ProjectRoot,
        [Parameter(Mandatory = $true)]
        [string] $RelativePath
    )

    $fullPath = Join-Path $ProjectRoot $RelativePath
    if (-not (Test-Path -LiteralPath $fullPath -PathType Leaf)) {
        throw "Missing required project file: $RelativePath"
    }
}

function Invoke-LeanGate {
    param(
        [Parameter(Mandatory = $true)]
        [string] $Label,
        [Parameter(Mandatory = $true)]
        [string] $WorkingDirectory,
        [Parameter(Mandatory = $true)]
        [string] $Executable,
        [Parameter(Mandatory = $true)]
        [string[]] $Arguments
    )

    Write-Host "STAGE: $Label"
    Push-Location -LiteralPath $WorkingDirectory
    try {
        $output = @(& $Executable @Arguments 2>&1)
        $processExitCode = $LASTEXITCODE
        foreach ($line in $output) {
            Write-Host $line
        }
        if ($processExitCode -ne 0) {
            throw "$Label failed with exit code $processExitCode."
        }
        $warnings = @($output | Where-Object { "$_" -match '^\s*warning:' })
        if ($warnings.Count -ne 0) {
            throw "$Label emitted $($warnings.Count) Lean warning(s)."
        }
        Write-Host "PASS: $Label"
    }
    finally {
        Pop-Location
    }
}

try {
    $projectRoot = Split-Path -Parent $PSScriptRoot
    $extensionRoot = Join-Path $projectRoot 'Extension'
    $logDirectory = Join-Path $projectRoot 'logs'
    if (-not (Test-Path -LiteralPath $logDirectory -PathType Container)) {
        New-Item -ItemType Directory -Path $logDirectory -ErrorAction Stop | Out-Null
    }

    $logStamp = Get-Date -Format 'yyyyMMdd-HHmmss'
    $logId = [guid]::NewGuid().ToString('N').Substring(0, 8)
    $buildLogPath = Join-Path $logDirectory "tao-trudgian-yang-build-$logStamp-$logId.log"
    Start-Transcript -LiteralPath $buildLogPath -NoClobber -ErrorAction Stop | Out-Null
    $buildTranscriptActive = $true

    Write-Host 'Tao--Trudgian--Yang 2025 verification runner'
    Write-Host "Project root: $projectRoot"
    Write-Host "Reproducibility log: $buildLogPath"

    Write-Host 'STAGE: project inventory'
    $requiredFiles = @(
        'README.md',
        'Tao-Trudgian-Yang Architecture.md',
        'Tao-Trudgian-Yang Checklist.md',
        'Tao-Trudgian-Yang Crosswalk.md',
        'Tao-Trudgian-Yang Goal Prompt.md',
        'Tao-Trudgian-Yang Reproduction Manifest.md',
        'Tao-Trudgian-Yang Research Agenda.md',
        'Tao-Trudgian-Yang Sources.md',
        'Dependencies\README.md',
        'Extension\README.md',
        'Sources\PINS.md',
        'Sources\SHA256SUMS.txt',
        'Tools\README.md',
        'Tools\verify_sources.ps1',
        'Tools\run_tao_trudgian_yang_build.ps1',
        'run_tao_trudgian_yang_build.bat',
        'push_to_github.bat'
    )
    foreach ($relativePath in $requiredFiles) {
        Assert-ProjectFile -ProjectRoot $projectRoot -RelativePath $relativePath
    }
    Write-Host "PASS: project inventory ($($requiredFiles.Count) required files)"

    Write-Host 'STAGE: pinned source integrity'
    & (Join-Path $PSScriptRoot 'verify_sources.ps1')
    Write-Host 'PASS: pinned source integrity'

    Write-Host 'STAGE: forbidden Lean shortcut scan'
    $leanFiles = @(
        Get-ChildItem -LiteralPath $projectRoot -Recurse -File -Filter '*.lean' |
            Where-Object { $_.FullName -notmatch '[\\/]\.lake[\\/]' }
    )
    $forbiddenPatterns = @(
        '\b(sorry|admit)\b|sorryAx',
        '^\s*(axiom|constant)\b',
        '\b(native_decide|implemented_by|unsafe)\b'
    )
    $forbiddenMatches = [System.Collections.Generic.List[string]]::new()
    foreach ($leanFile in $leanFiles) {
        foreach ($pattern in $forbiddenPatterns) {
            foreach ($match in Select-String -LiteralPath $leanFile.FullName -Pattern $pattern -CaseSensitive) {
                $relativeLeanPath = $leanFile.FullName.Substring($projectRoot.Length + 1)
                $forbiddenMatches.Add("$relativeLeanPath`:$($match.LineNumber): $($match.Line.Trim())")
            }
        }
    }
    if ($forbiddenMatches.Count -ne 0) {
        foreach ($forbiddenMatch in $forbiddenMatches) {
            Write-Host "FORBIDDEN: $forbiddenMatch"
        }
        throw "Forbidden Lean shortcut scan found $($forbiddenMatches.Count) match(es)."
    }
    Write-Host "PASS: forbidden Lean shortcut scan ($($leanFiles.Count) Lean files)"

    $lakefilePath = Join-Path $extensionRoot 'lakefile.toml'
    $toolchainPath = Join-Path $extensionRoot 'lean-toolchain'
    $hasLakefile = Test-Path -LiteralPath $lakefilePath -PathType Leaf
    $hasToolchain = Test-Path -LiteralPath $toolchainPath -PathType Leaf

    if ($hasLakefile -ne $hasToolchain) {
        throw 'Extension bootstrap is incomplete: lakefile.toml and lean-toolchain must be installed together.'
    }

    if (-not $hasLakefile) {
        Write-Host ''
        Write-Host 'FINAL RESULT: PLANNING SCAFFOLD PASS'
        Write-Host 'PLANNING SCAFFOLD ONLY: no Lean package, theorem build, semantic regression, or axiom audit was run.'
        Write-Host 'Install the EPZAE-01 unified toolchain/package before treating this command as Lean verification.'
        Write-Host "Reproducibility log: $buildLogPath"
        $buildExitCode = 0
    }
    else {
        Write-Host 'STAGE: Lean package bootstrap inventory'
        $leanPackageFiles = @(
            'Extension\TaoTrudgianYang2025.lean',
            'Extension\TaoTrudgianYang2025\Audit.lean',
            'Extension\TaoTrudgianYang2025\SemanticRegression.lean'
        )
        foreach ($relativePath in $leanPackageFiles) {
            Assert-ProjectFile -ProjectRoot $projectRoot -RelativePath $relativePath
        }
        Write-Host 'PASS: Lean package bootstrap inventory'

        $lakeCommand = Get-Command lake -ErrorAction Stop
        Invoke-LeanGate -Label 'default Lake build' -WorkingDirectory $extensionRoot `
            -Executable $lakeCommand.Source -Arguments @('build')
        Invoke-LeanGate -Label 'semantic regression' -WorkingDirectory $extensionRoot `
            -Executable $lakeCommand.Source -Arguments @(
                'env', 'lean', 'TaoTrudgianYang2025\SemanticRegression.lean'
            )
        Invoke-LeanGate -Label 'transitive axiom audit' -WorkingDirectory $extensionRoot `
            -Executable $lakeCommand.Source -Arguments @(
                'env', 'lean', 'TaoTrudgianYang2025\Audit.lean'
            )

        Write-Host ''
        Write-Host 'FINAL RESULT: LEAN VERIFICATION PASS'
        Write-Host 'This verifies the installed package scope; it does not by itself mark any paper theorem complete.'
        Write-Host "Reproducibility log: $buildLogPath"
        $buildExitCode = 0
    }
}
catch {
    Write-Host ''
    Write-Host "FINAL RESULT: FAIL - $($_.Exception.Message)"
    if ($buildLogPath) {
        Write-Host "Reproducibility log: $buildLogPath"
    }
    $buildExitCode = 1
}
finally {
    if ($buildTranscriptActive) {
        Stop-Transcript -ErrorAction SilentlyContinue | Out-Null
    }
}

exit $buildExitCode

