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
        'Tao-Trudgian-Yang Energy Powering Repair.md',
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
            'Extension\TaoTrudgianYang2025\EnergyPowering.lean',
            'Extension\TaoTrudgianYang2025\EnergyPoweredPatterns.lean',
            'Extension\TaoTrudgianYang2025\EnergyPoweringLimits.lean',
            'Extension\TaoTrudgianYang2025\CorrectedEnergyPowering.lean',
            'Extension\TaoTrudgianYang2025\EnergyPoweringBounds.lean',
            'Extension\TaoTrudgianYang2025\EnergyLogLimits.lean',
            'Extension\TaoTrudgianYang2025\HeathBrownEnergyFinite.lean',
            'Extension\TaoTrudgianYang2025\HeathBrownEnergy.lean',
            'Extension\TaoTrudgianYang2025\ClassicalLargeValueRegions.lean',
            'Extension\TaoTrudgianYang2025\EnergyClauseOneGeneral.lean',
            'Extension\TaoTrudgianYang2025\EnergyClauseOneZeta.lean',
            'Extension\TaoTrudgianYang2025\ZetaMomentKernel.lean',
            'Extension\TaoTrudgianYang2025\ZetaMomentTransfer.lean',
            'Extension\TaoTrudgianYang2025\ZetaMomentAsymptotics.lean',
            'Extension\TaoTrudgianYang2025\ZetaIntervalCutoff.lean',
            'Extension\TaoTrudgianYang2025\ZetaMellinEntry.lean',
            'Extension\TaoTrudgianYang2025\ZetaMellinContour.lean',
            'Extension\TaoTrudgianYang2025\ZetaMellinShift.lean',
            'Extension\TaoTrudgianYang2025\ZetaCutoffDerivatives.lean',
            'Extension\TaoTrudgianYang2025\ZetaMellinDerivative.lean',
            'Extension\TaoTrudgianYang2025\ZetaMellinUniform.lean',
            'Extension\TaoTrudgianYang2025\ZetaMellinLocalization.lean',
            'Extension\TaoTrudgianYang2025\ZetaPerronEntry.lean',
            'Extension\TaoTrudgianYang2025\ZetaShortPerron.lean',
            'Extension\TaoTrudgianYang2025\ZetaShortPatterns.lean',
            'Extension\TaoTrudgianYang2025\ZetaLargeValueDiscreteness.lean',
            'Extension\TaoTrudgianYang2025\ZetaPointwiseNonexistence.lean',
            'Extension\TaoTrudgianYang2025\ZetaSquareContour.lean',
            'Extension\TaoTrudgianYang2025\ZetaSquareContourShift.lean',
            'Extension\TaoTrudgianYang2025\ZetaSquareDivisorKernel.lean',
            'Extension\TaoTrudgianYang2025\ZetaSquareDivisorSeries.lean',
            'Extension\TaoTrudgianYang2025\ZetaSquareSourceEntry.lean',
            'Extension\TaoTrudgianYang2025\ZetaSquareLocalMean.lean',
            'Extension\TaoTrudgianYang2025\ZetaSquareAveraging.lean',
            'Extension\TaoTrudgianYang2025\ZetaSquareGaussianTail.lean',
            'Extension\TaoTrudgianYang2025\ZetaSquareGaussianTransform.lean',
            'Extension\TaoTrudgianYang2025\ZetaDigammaLog.lean',
            'Extension\TaoTrudgianYang2025\ZetaSquareGammaPhase.lean',
            'Extension\TaoTrudgianYang2025\ZetaSquareGammaQuadratic.lean',
            'Extension\TaoTrudgianYang2025\ZetaSquareGammaTransform.lean',
            'Extension\TaoTrudgianYang2025\ZetaGammaShiftLog.lean',
            'Extension\TaoTrudgianYang2025\ZetaGammaShiftAmplitude.lean',
            'Extension\TaoTrudgianYang2025\ZetaSquarePoleShift.lean',
            'Extension\TaoTrudgianYang2025\ZetaSquareNearKernel.lean',
            'Extension\TaoTrudgianYang2025\ZetaSquareGammaInverse.lean',
            'Extension\TaoTrudgianYang2025\ZetaSquareKernelApproximation.lean',
            'Extension\TaoTrudgianYang2025\ZetaSquareLeadingDivisor.lean',
            'Extension\TaoTrudgianYang2025\ZetaDivisorWeightKernel.lean',
            'Extension\TaoTrudgianYang2025\ZetaDivisorWeightReflection.lean',
            'Extension\TaoTrudgianYang2025\ZetaDivisorWeightSource.lean',
            'Extension\TaoTrudgianYang2025\ZetaDivisorWeightVariation.lean',
            'Extension\TaoTrudgianYang2025\ZetaDivisorWeightMass.lean',
            'Extension\TaoTrudgianYang2025\ZetaDivisorWeightFreezing.lean',
            'Extension\TaoTrudgianYang2025\ZetaFrozenDivisorGaussian.lean',
            'Extension\TaoTrudgianYang2025\ZetaSquareRealSource.lean',
            'Extension\TaoTrudgianYang2025\ZetaSquareFrozenWindow.lean',
            'Extension\TaoTrudgianYang2025\ZetaQuadraticDivisorBand.lean',
            'Extension\TaoTrudgianYang2025\ZetaQuadraticDivisorShortening.lean',
            'Extension\TaoTrudgianYang2025\ZetaSourceLogScales.lean',
            'Extension\TaoTrudgianYang2025\ZetaSourceErrorScales.lean',
            'Extension\TaoTrudgianYang2025\ZetaShortDivisorSource.lean',
            'Extension\TaoTrudgianYang2025\ZetaShortDivisorGeometry.lean',
            'Extension\TaoTrudgianYang2025\ZetaDivisorWeightSmooth.lean',
            'Extension\TaoTrudgianYang2025\ZetaDivisorTestSmooth.lean',
            'Extension\TaoTrudgianYang2025\ZetaDivisorBandCutoff.lean',
            'Extension\TaoTrudgianYang2025\ZetaSmoothDivisorTest.lean',
            'Extension\TaoTrudgianYang2025\ZetaDivisorVoronoi.lean',
            'Extension\TaoTrudgianYang2025\ZetaSmoothDivisorTail.lean',
            'Extension\TaoTrudgianYang2025\ZetaSquareVoronoiSource.lean',
            'Extension\TaoTrudgianYang2025\ZetaDivisorBesselSource.lean',
            'Extension\TaoTrudgianYang2025\ZetaBesselK0Decay.lean',
            'Extension\TaoTrudgianYang2025\ZetaSmoothDivisorSupport.lean',
            'Extension\TaoTrudgianYang2025\ZetaSmoothDivisorMass.lean',
            'Extension\TaoTrudgianYang2025\ZetaBesselK0Integral.lean',
            'Extension\TaoTrudgianYang2025\ZetaBesselK0Series.lean',
            'Extension\TaoTrudgianYang2025\ZetaBesselK0Scales.lean',
            'Extension\TaoTrudgianYang2025\ZetaSquareBesselMinusSource.lean',
            'Extension\TaoTrudgianYang2025\ZetaDivisorLatticePhase.lean',
            'Extension\TaoTrudgianYang2025\ZetaAtkinsonVoronoi.lean',
            'Extension\TaoTrudgianYang2025\ZetaAtkinsonK0.lean',
            'Extension\TaoTrudgianYang2025\ZetaAtkinsonReducedSource.lean',
            'Extension\TaoTrudgianYang2025\ZetaAtkinsonPhase.lean',
            'Extension\TaoTrudgianYang2025\ZetaAtkinsonSaddle.lean',
            'Extension\TaoTrudgianYang2025\IntervalAmplitudeBounds.lean',
            'Extension\TaoTrudgianYang2025\ZetaMainElementaryWeights.lean',
            'Extension\TaoTrudgianYang2025\ZetaMainMellinProfile.lean',
            'Extension\TaoTrudgianYang2025\ZetaLogGaussianVariation.lean',
            'Extension\TaoTrudgianYang2025\ZetaQuadraticGaussianDerivative.lean',
            'Extension\TaoTrudgianYang2025\ZetaQuadraticLogGaussianVariation.lean',
            'Extension\TaoTrudgianYang2025\ZetaAtkinsonMainWeight.lean',
            'Extension\TaoTrudgianYang2025\ZetaAtkinsonMainIntegral.lean',
            'Extension\TaoTrudgianYang2025\ZetaAtkinsonMinusSource.lean',
            'Extension\TaoTrudgianYang2025\NeumannContourKernel.lean',
            'Extension\TaoTrudgianYang2025\NeumannContourShift.lean',
            'Extension\TaoTrudgianYang2025\NeumannSchlafliEntry.lean',
            'Extension\TaoTrudgianYang2025\NeumannLaplaceRepresentation.lean',
            'Extension\TaoTrudgianYang2025\NeumannLaplaceAmplitude.lean',
            'Extension\TaoTrudgianYang2025\NeumannRayFactorization.lean',
            'Extension\TaoTrudgianYang2025\NeumannLaplaceMoments.lean',
            'Extension\TaoTrudgianYang2025\NeumannLaplaceRemainder.lean',
            'Extension\TaoTrudgianYang2025\NeumannTwoTermExpansion.lean',
            'Extension\TaoTrudgianYang2025\NeumannSourceBounds.lean',
            'Extension\TaoTrudgianYang2025\ZetaNeumannRemainder.lean',
            'Extension\TaoTrudgianYang2025\ZetaNeumannSeries.lean',
            'Extension\TaoTrudgianYang2025\ZetaAtkinsonTwoTermSource.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonRootPhase.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonFirstDerivative.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonRootIntegral.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonAmplitudeIntegral.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonPowerWeight.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonPowerIntegral.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonCarrierAlgebra.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonCarrierIntegrals.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonCarrierBounds.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonCarrierSource.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonFrequencyTail.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonCorrectionBounds.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonLeadingSeries.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonLeadingSource.lean',
            'Extension\TaoTrudgianYang2025\ZetaQuadraticGaussianSecondDerivative.lean',
            'Extension\TaoTrudgianYang2025\IntervalSecondDerivativeBounds.lean',
            'Extension\TaoTrudgianYang2025\ZetaBandSecondDerivatives.lean',
            'Extension\TaoTrudgianYang2025\ZetaBandPhysicalDerivatives.lean',
            'Extension\TaoTrudgianYang2025\SecondDerivativeComposition.lean',
            'Extension\TaoTrudgianYang2025\ZetaGaussianProfileSecondDerivatives.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonPhaseSecondDerivatives.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonRootAmplitudeDerivatives.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonRootFourierSupport.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonRootFourierDecay.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonFourierSource.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonSecondOrderTail.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonLeadingMajorant.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonLeadingTruncation.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonFiniteSource.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonSaddleNormalization.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonSaddlePhase.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonSaddleGaussian.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonSaddleTaylor.lean',
            'Extension\TaoTrudgianYang2025\ZetaGaussianNaturalDerivatives.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonNaturalAmplitude.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonLocalStationary.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonStationaryTails.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonStationaryReduction.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonFiniteStationaryMain.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonSignedStationaryMain.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonStationaryPhysical.lean',
            'Extension\TaoTrudgianYang2025\ContinuousKernelPrimitive.lean',
            'Extension\TaoTrudgianYang2025\FresnelDampedTails.lean',
            'Extension\TaoTrudgianYang2025\FresnelGaussianComparison.lean',
            'Extension\TaoTrudgianYang2025\FresnelAbelLimit.lean',
            'Extension\TaoTrudgianYang2025\FresnelEvaluation.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonStationaryMain.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonStationaryEvaluation.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonEvaluatedPhases.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonStationaryPowerSaving.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonSaddleSupport.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonRootBand.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonBandCancellation.lean',
            'Extension\TaoTrudgianYang2025\ReciprocalSecondDerivativeBounds.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonSecondOrderIntegration.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonSlopeDerivativeBounds.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonBandAmplitude.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonBandSecondOrder.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonSharpTruncation.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonSourceBand.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonSourceCutoff.lean',
            'Extension\TaoTrudgianYang2025\StationaryOddRemainder.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonSymmetricStationary.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonSymmetricReduction.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonSymmetricBalance.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonFourthRootRadius.lean',
            'Extension\TaoTrudgianYang2025\DivisorQuarterPrefix.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonStationarySeries.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonStationarySumScale.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonStationarySumError.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonStationaryZetaSource.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonMainNormalization.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonSignedPhaseSeries.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonMainPartialSummation.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonMainWeightBounds.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonMainZetaConsumer.lean',
            'Extension\TaoTrudgianYang2025\FiniteWeightVariation.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonGaussianVariation.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonSaddleSamples.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonResidualVariation.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonMainVariation.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonPhaseBlockBound.lean',
            'Extension\TaoTrudgianYang2025\TruncatedDyadicPartition.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonDyadicMain.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonDyadicZetaConsumer.lean',
            'Extension\TaoTrudgianYang2025\FinitePrefixGram.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonPrefixVectors.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonMaximalGram.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonCoefficientEnergy.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonDyadicGramBudget.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonPacketGram.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonLocalMeanGram.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonGramPhysicalCutoff.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonIndexPhase.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonIndexCurvature.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonIndexHeight.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonIndexScales.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonIndexBProcess.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonIndexFirstDerivative.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonPrefixCancellation.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonPrefixGapBound.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonGramCutoffGeometry.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonGapBudget.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonGapPacketConsumers.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonGapArithmetic.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonArithmeticGapPackets.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonNearGap.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonSeparatedReciprocal.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonNearGapBudget.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonSeparatedNearPackets.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonFarCurvature.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonFarRadical.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonFarGap.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonLocalizedGapBudget.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonLocalizedPowers.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonPowerGapBudget.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonPowerGapPackets.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonPhysicalLogs.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonCutoffPowers.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonPhysicalTerm.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonPhysicalBudget.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonPhysicalPackets.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonCardinalityAbsorption.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonHeightCover.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonGlobalCardinality.lean',
            'Extension\TaoTrudgianYang2025\AtkinsonLocalMeanCounting.lean',
            'Extension\TaoTrudgianYang2025\PointMeanDigamma.lean',
            'Extension\TaoTrudgianYang2025\PointMeanGammaShift.lean',
            'Extension\TaoTrudgianYang2025\PointMeanGammaDecay.lean',
            'Extension\TaoTrudgianYang2025\PointMeanGammaKernel.lean',
            'Extension\TaoTrudgianYang2025\PointMeanGammaConvolution.lean',
            'Extension\TaoTrudgianYang2025\PointMeanExponentialOverlap.lean',
            'Extension\TaoTrudgianYang2025\PointMeanIntegralOverlap.lean',
            'Extension\TaoTrudgianYang2025\PointMeanGammaProduct.lean',
            'Extension\TaoTrudgianYang2025\PointMeanMellinExp.lean',
            'Extension\TaoTrudgianYang2025\PointMeanDivisorMellin.lean',
            'Extension\TaoTrudgianYang2025\PointMeanDoublePole.lean',
            'Extension\TaoTrudgianYang2025\PointMeanMovingPole.lean',
            'Extension\TaoTrudgianYang2025\PointMeanGammaPole.lean',
            'Extension\TaoTrudgianYang2025\PointMeanContourBasic.lean',
            'Extension\TaoTrudgianYang2025\PointMeanMellinHorizontal.lean',
            'Extension\TaoTrudgianYang2025\PointMeanMellinVertical.lean',
            'Extension\TaoTrudgianYang2025\PointMeanMellinShift.lean',
            'Extension\TaoTrudgianYang2025\PointMeanMellinBounds.lean',
            'Extension\TaoTrudgianYang2025\PointMeanOffCritical.lean',
            'Extension\TaoTrudgianYang2025\PointMeanReflection.lean',
            'Extension\TaoTrudgianYang2025\PointMeanOffCriticalStrong.lean',
            'Extension\TaoTrudgianYang2025\PointMeanLemmaThreeStatement.lean',
            'Extension\TaoTrudgianYang2025\PointMeanLemmaThreeContour.lean',
            'Extension\TaoTrudgianYang2025\PointMeanLemmaThreeDouble.lean',
            'Extension\TaoTrudgianYang2025\PointMeanLemmaThreeEdges.lean',
            'Extension\TaoTrudgianYang2025\PointMeanLemmaThreeTail.lean',
            'Extension\TaoTrudgianYang2025\PointMeanEquation44.lean',
            'Extension\TaoTrudgianYang2025\FiniteOccupancy.lean',
            'Extension\TaoTrudgianYang2025\PointClusters.lean',
            'Extension\TaoTrudgianYang2025\PointClusterEntry.lean',
            'Extension\TaoTrudgianYang2025\PointClusterCounting.lean',
            'Extension\TaoTrudgianYang2025\PointValueWidth.lean',
            'Extension\TaoTrudgianYang2025\PointValueGrowth.lean',
            'Extension\TaoTrudgianYang2025\PointValueRanges.lean',
            'Extension\TaoTrudgianYang2025\PointValueMeasure.lean',
            'Extension\TaoTrudgianYang2025\TruncatedLayerCake.lean',
            'Extension\TaoTrudgianYang2025\PointValueTailIntegral.lean',
            'Extension\TaoTrudgianYang2025\PointValueHighMoment.lean',
            'Extension\TaoTrudgianYang2025\PointValueLowMoment.lean',
            'Extension\TaoTrudgianYang2025\ZetaFourthSource.lean',
            'Extension\TaoTrudgianYang2025\ZetaFourthGaussian.lean',
            'Extension\TaoTrudgianYang2025\ZetaFourthKernelBasic.lean',
            'Extension\TaoTrudgianYang2025\ZetaFourthKernelNear.lean',
            'Extension\TaoTrudgianYang2025\ZetaFourthKernelFar.lean',
            'Extension\TaoTrudgianYang2025\ZetaFourthKernel.lean',
            'Extension\TaoTrudgianYang2025\ZetaFourthContourBounds.lean',
            'Extension\TaoTrudgianYang2025\ZetaFourthTerm.lean',
            'Extension\TaoTrudgianYang2025\ZetaFourthTermBounds.lean',
            'Extension\TaoTrudgianYang2025\ZetaFourthContourShift.lean',
            'Extension\TaoTrudgianYang2025\ZetaFourthContributionBounds.lean',
            'Extension\TaoTrudgianYang2025\ZetaFourthTruncation.lean',
            'Extension\TaoTrudgianYang2025\ZetaFourthTailPower.lean',
            'Extension\TaoTrudgianYang2025\ZetaFourthTailScale.lean',
            'Extension\TaoTrudgianYang2025\DirichletMeanSquareTranslation.lean',
            'Extension\TaoTrudgianYang2025\DirichletPrefixBlocks.lean',
            'Extension\TaoTrudgianYang2025\DirichletPrefixMeanSquare.lean',
            'Extension\TaoTrudgianYang2025\ZetaFourthCoefficients.lean',
            'Extension\TaoTrudgianYang2025\ZetaFourthCoefficientMass.lean',
            'Extension\TaoTrudgianYang2025\ZetaFourthPolynomialMean.lean',
            'Extension\TaoTrudgianYang2025\WeightedIntegralSquare.lean',
            'Extension\TaoTrudgianYang2025\DirichletPrefixBounded.lean',
            'Extension\TaoTrudgianYang2025\ZetaFourthPrefixGaussian.lean',
            'Extension\TaoTrudgianYang2025\GaussianPrefixMean.lean',
            'Extension\TaoTrudgianYang2025\DyadicMomentCutoff.lean',
            'Extension\TaoTrudgianYang2025\ZetaFourthDyadicBudget.lean',
            'Extension\TaoTrudgianYang2025\ZetaFourthMoment.lean',
            'Extension\TaoTrudgianYang2025\ZetaTwelfthMoment.lean',
            'Extension\TaoTrudgianYang2025\EnergyCardinalityBounds.lean',
        'Extension\TaoTrudgianYang2025\HeathBrownNineBranches.lean',
        'Extension\TaoTrudgianYang2025\EnergyClauseTwoCaps.lean',
        'Extension\TaoTrudgianYang2025\EnergyClauseTwoCertificates.lean',
        'Extension\TaoTrudgianYang2025\EnergyClauseTwoGeneral.lean',
        'Extension\TaoTrudgianYang2025\ZetaSixthLocalization.lean',
        'Extension\TaoTrudgianYang2025\ZetaSixthPerron.lean',
        'Extension\TaoTrudgianYang2025\ZetaBelowTwiceSigma.lean',
        'Extension\TaoTrudgianYang2025\ZetaTwelfthLowerShort.lean',
        'Extension\TaoTrudgianYang2025\EnergyClauseTwoZetaCertificates.lean',
        'Extension\TaoTrudgianYang2025\EnergyClauseTwo.lean',
        'Extension\TaoTrudgianYang2025\NewAdditiveEnergy.lean',
        'Extension\TaoTrudgianYang2025\JutilaGram.lean',
        'Extension\TaoTrudgianYang2025\JutilaPatternEntry.lean',
        'Extension\TaoTrudgianYang2025\JutilaPoweredMoments.lean',
        'Extension\TaoTrudgianYang2025\JutilaReflectedEntry.lean',
        'Extension\TaoTrudgianYang2025\JutilaPolynomialMoments.lean',
        'Extension\TaoTrudgianYang2025\JutilaPrefixMoments.lean',
        'Extension\TaoTrudgianYang2025\JutilaReflectionIntegrals.lean',
        'Extension\TaoTrudgianYang2025\JutilaTraceBins.lean',
        'Extension\TaoTrudgianYang2025\JutilaBinnedPatterns.lean',
        'Extension\TaoTrudgianYang2025\JutilaHybridPatterns.lean',
        'Extension\TaoTrudgianYang2025\JutilaDualScales.lean',
        'Extension\TaoTrudgianYang2025\JutilaPhysicalMain.lean',
        'Extension\TaoTrudgianYang2025\JutilaPhysicalPatterns.lean',
        'Extension\TaoTrudgianYang2025\JutilaSmoothingErrors.lean',
        'Extension\TaoTrudgianYang2025\JutilaSmoothingProfile.lean',
        'Extension\TaoTrudgianYang2025\JutilaSmoothingLosses.lean',
        'Extension\TaoTrudgianYang2025\JutilaSmoothedPatterns.lean',
            'Extension\TaoTrudgianYang2025\ZetaTwelfthFromMoment.lean',
            'Extension\TaoTrudgianYang2025\EnergyClauseOneFromMoment.lean',
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
