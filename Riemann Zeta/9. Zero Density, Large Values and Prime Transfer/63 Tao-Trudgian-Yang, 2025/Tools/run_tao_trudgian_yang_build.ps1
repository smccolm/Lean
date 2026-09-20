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
        $warnings = @($output | Where-Object { "$_" -match '(^|\s)warning:' })
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
        'Tao-Trudgian-Yang Energy Powering Obstruction.md',
        'Tao-Trudgian-Yang Reproduction Manifest.md',
        'Tao-Trudgian-Yang Research Agenda.md',
        'Tao-Trudgian-Yang Sources.md',
        'Dependencies\README.md',
        'Dependencies\ANTEDBFrozen\README.md',
        'Dependencies\ANTEDBFrozen\LICENSE',
        'Dependencies\ANTEDBFrozen\SOURCE_SHA256SUMS.txt',
        'Dependencies\ANTEDBFrozen\lakefile.toml',
        'Dependencies\ANTEDBFrozen\lean-toolchain',
        'Extension\README.md',
        'Extension\lake-manifest.json',
        'Extension\lakefile.toml',
        'Extension\lean-toolchain',
        'Sources\PINS.md',
        'Sources\SHA256SUMS.txt',
        'Tools\README.md',
        'Tools\generate_certificates.py',
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

    Write-Host 'STAGE: frozen ANTEDB source integrity'
    $frozenRoot = Join-Path $projectRoot 'Dependencies\ANTEDBFrozen'
    $frozenLedger = Join-Path $frozenRoot 'SOURCE_SHA256SUMS.txt'
    $frozenLines = @(
        Get-Content -LiteralPath $frozenLedger |
            Where-Object { -not [string]::IsNullOrWhiteSpace($_) }
    )
    if ($frozenLines.Count -ne 12) {
        throw "Frozen ANTEDB manifest must contain exactly 12 files; found $($frozenLines.Count)."
    }
    $manifestPaths = [System.Collections.Generic.HashSet[string]]::new(
        [System.StringComparer]::OrdinalIgnoreCase)
    foreach ($line in $frozenLines) {
        if ($line -notmatch '^([0-9A-Fa-f]{64})  (.+)$') {
            throw "Malformed frozen-source hash line: $line"
        }
        $expectedHash = $Matches[1].ToUpperInvariant()
        $relativePath = $Matches[2].Replace('/', '\')
        if (-not $manifestPaths.Add($relativePath)) {
            throw "Duplicate frozen-source manifest entry: $relativePath"
        }
        $sourcePath = Join-Path $frozenRoot $relativePath
        if (-not (Test-Path -LiteralPath $sourcePath -PathType Leaf)) {
            throw "Frozen ANTEDB source is missing: $relativePath"
        }
        $actualHash = (Get-FileHash -LiteralPath $sourcePath -Algorithm SHA256).Hash
        if ($actualHash -ne $expectedHash) {
            throw "Frozen ANTEDB source hash mismatch: $relativePath"
        }
    }
    $actualFrozenFiles = @(
        Get-ChildItem -LiteralPath $frozenRoot -Recurse -File |
            Where-Object { $_.Extension -eq '.lean' -or $_.Name -eq 'LICENSE' } |
            ForEach-Object { $_.FullName.Substring($frozenRoot.Length + 1) }
    )
    foreach ($relativePath in $actualFrozenFiles) {
        if (-not $manifestPaths.Contains($relativePath)) {
            throw "Unmanifested frozen ANTEDB source: $relativePath"
        }
    }
    if ($actualFrozenFiles.Count -ne $frozenLines.Count) {
        throw 'Frozen ANTEDB source inventory does not match its hash manifest.'
    }
    Write-Host "PASS: frozen ANTEDB source integrity ($($frozenLines.Count) files)"

    Write-Host 'STAGE: forbidden Lean shortcut scan'
    $leanFiles = @(
        Get-ChildItem -LiteralPath $projectRoot -Recurse -File -Filter '*.lean' |
            Where-Object { $_.FullName -notmatch '[\\/]\.lake[\\/]' }
    )
    $forbiddenPatterns = @(
        '\b(sorry|admit)\b|sorryAx',
        '^\s*(axiom|constant)\s+[^:\s]',
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
            'Extension\TaoTrudgianYang2025\AdditiveEnergy.lean',
            'Extension\TaoTrudgianYang2025\AsymptoticBridge.lean',
            'Extension\TaoTrudgianYang2025\Audit.lean',
            'Extension\TaoTrudgianYang2025\BetaDuality.lean',
            'Extension\TaoTrudgianYang2025\BourgainPiecewiseCertificates.lean',
            'Extension\TaoTrudgianYang2025\ClassicalDensityBridge.lean',
            'Extension\TaoTrudgianYang2025\ClassicalTypeIEnergyTransfer.lean',
            'Extension\TaoTrudgianYang2025\ClassicalTypeIUniformity.lean',
            'Extension\TaoTrudgianYang2025\ClassicalTypeIIEnergyTransfer.lean',
            'Extension\TaoTrudgianYang2025\ClassicalSlabEnergyTransfer.lean',
            'Extension\TaoTrudgianYang2025\ZeroEnergyAssembly.lean',
            'Extension\TaoTrudgianYang2025\EnergyExponentTransfer.lean',
            'Extension\TaoTrudgianYang2025\EnergyPoweringObstruction.lean',
            'Extension\TaoTrudgianYang2025\EnergyExponents.lean',
            'Extension\TaoTrudgianYang2025\EnergyUniformity.lean',
            'Extension\TaoTrudgianYang2025\EnergyCertificates.lean',
            'Extension\TaoTrudgianYang2025\EnergyBoundAsymptotics.lean',
            'Extension\TaoTrudgianYang2025\EnergyRegionAsymptotics.lean',
            'Extension\TaoTrudgianYang2025\EnergyRegionSupremum.lean',
            'Extension\TaoTrudgianYang2025\EnergyRegions.lean',
            'Extension\TaoTrudgianYang2025\ExponentPair.lean',
            'Extension\TaoTrudgianYang2025\GeneratedCertificates.lean',
            'Extension\TaoTrudgianYang2025\GuthMaynardBridge.lean',
            'Extension\TaoTrudgianYang2025\LargeValueExponent.lean',
            'Extension\TaoTrudgianYang2025\LargeValuePattern.lean',
            'Extension\TaoTrudgianYang2025\PiecewiseEnvelope.lean',
            'Extension\TaoTrudgianYang2025\PolyhedralCertificates.lean',
            'Extension\TaoTrudgianYang2025\RationalCertificates.lean',
            'Extension\TaoTrudgianYang2025\SemanticRegression.lean',
            'Extension\TaoTrudgianYang2025\ToleranceNormalization.lean',
            'Extension\TaoTrudgianYang2025\EnergyPartition.lean',
            'Extension\TaoTrudgianYang2025\EnergySeparation.lean',
            'Extension\TaoTrudgianYang2025\DetectorPattern.lean',
            'Extension\TaoTrudgianYang2025\ZeroCountBridge.lean',
            'Extension\TaoTrudgianYang2025\ZeroDensityExponent.lean',
            'Extension\TaoTrudgianYang2025\ZeroEnergyMultiplicity.lean',
            'Extension\TaoTrudgianYang2025\ZeroEnergyTypeI.lean',
            'Extension\TaoTrudgianYang2025\ZeroEnergyDichotomy.lean'
        )
        foreach ($relativePath in $leanPackageFiles) {
            Assert-ProjectFile -ProjectRoot $projectRoot -RelativePath $relativePath
        }
        $listedLeanFiles = [System.Collections.Generic.HashSet[string]]::new(
            [string[]]$leanPackageFiles, [System.StringComparer]::OrdinalIgnoreCase)
        $rootImports = Get-Content -LiteralPath (
            Join-Path $extensionRoot 'TaoTrudgianYang2025.lean') -Raw
        $explicitLeanGates = @(
            'TaoTrudgianYang2025.Audit',
            'TaoTrudgianYang2025.SemanticRegression'
        )
        $actualLeanFiles = @(
            Get-ChildItem -LiteralPath $extensionRoot -Recurse -File -Filter '*.lean' |
                Where-Object { $_.FullName -notmatch '[\\/]\.lake[\\/]' }
        )
        foreach ($leanFile in $actualLeanFiles) {
            $relativePath = $leanFile.FullName.Substring($projectRoot.Length + 1)
            if (-not $listedLeanFiles.Contains($relativePath)) {
                throw "Unlisted Lean package file: $relativePath"
            }
            $modulePath = $leanFile.FullName.Substring($extensionRoot.Length + 1)
            $moduleName = $modulePath.Substring(0, $modulePath.Length - 5).Replace('\', '.')
            if ($moduleName -eq 'TaoTrudgianYang2025' -or
                $explicitLeanGates -contains $moduleName) {
                continue
            }
            $importPattern = '(?m)^import\s+' + [regex]::Escape($moduleName) + '\s*$'
            if ($rootImports -notmatch $importPattern) {
                throw "Production module missing from the root import graph: $moduleName"
            }
        }
        Write-Host "PASS: complete production coverage ($($actualLeanFiles.Count) Lean package files)"
        Write-Host 'PASS: Lean package bootstrap inventory'

        Write-Host 'STAGE: deterministic certificate regeneration'
        $pythonCommand = Get-Command python -ErrorAction Stop
        $generatorPath = Join-Path $projectRoot 'Tools\generate_certificates.py'
        $archivePath = Join-Path $projectRoot 'Sources\antedb-expdb-paper-time-9953003.zip'
        $checkedCertificatePath = Join-Path $extensionRoot `
            'TaoTrudgianYang2025\GeneratedCertificates.lean'
        $temporaryCertificate = New-TemporaryFile
        try {
            & $pythonCommand.Source $generatorPath --archive $archivePath `
                --output $temporaryCertificate.FullName
            if ($LASTEXITCODE -ne 0) {
                throw "Certificate generator exited with code $LASTEXITCODE."
            }
            $expectedHash = (Get-FileHash -LiteralPath $checkedCertificatePath `
                -Algorithm SHA256).Hash
            $actualHash = (Get-FileHash -LiteralPath $temporaryCertificate.FullName `
                -Algorithm SHA256).Hash
            if ($actualHash -ne $expectedHash) {
                throw 'Generated certificate output differs from the checked-in Lean module.'
            }
        }
        finally {
            Remove-Item -LiteralPath $temporaryCertificate.FullName -Force `
                -ErrorAction SilentlyContinue
        }
        Write-Host 'PASS: deterministic certificate regeneration'

        $lakeCommand = Get-Command lake -ErrorAction Stop
        if ([string]::IsNullOrWhiteSpace($env:ELAN_HOME)) {
            $elanBin = Split-Path -Parent $lakeCommand.Source
            $elanHomeCandidate = Split-Path -Parent $elanBin
            $toolchainDirectory = Join-Path $elanHomeCandidate 'toolchains'
            if (-not (Test-Path -LiteralPath $toolchainDirectory -PathType Container)) {
                throw 'ELAN_HOME is unset and could not be inferred from the Lake executable.'
            }
            $env:ELAN_HOME = $elanHomeCandidate
            Write-Host "Using inferred ELAN_HOME: $elanHomeCandidate"
        }
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
