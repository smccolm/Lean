$ErrorActionPreference = 'Stop'

try {
    $nodeRoot = Split-Path -Parent $PSScriptRoot
    $extensionRoot = Join-Path $nodeRoot 'Extension'

    $requiredFiles = @(
        'README.md',
        'Tao Architecture.md',
        'Tao Checklist.md',
        'Tao Crosswalk.md',
        'Tao Goal Prompt.md',
        'Tao Reproduction Manifest.md',
        'Tao Research Agenda.md',
        'Tao Sources.md',
        'Dependencies\README.md',
        'Dependencies\GafniTaoFrozen\README.md',
        'Dependencies\GafniTaoFrozen\SOURCE_SHA256SUMS.txt',
        'Dependencies\GafniTaoFrozen\lake-manifest.json',
        'Dependencies\GafniTaoFrozen\lakefile.toml',
        'Dependencies\GafniTaoFrozen\lean-toolchain',
        'Dependencies\GafniTaoFrozen\GafniTao\Theorem11.lean',
        'Dependencies\GafniTaoFrozen\GafniTao\WooleySourceCriticalBase.lean',
        'Dependencies\GafniTaoFrozen\GafniTao\WooleySourceToPadic.lean',
        'Dependencies\GafniTaoFrozen\GafniTao\WooleyPadicToCritical.lean',
        'Dependencies\GafniTaoFrozen\PrimeNumberTheoremAndClean\lakefile.toml',
        'Extension\lake-manifest.json',
        'Extension\lakefile.toml',
        'Extension\lean-toolchain',
        'Extension\Tao2026.lean',
        'Extension\Tao2026\Anatomy.lean',
        'Extension\Tao2026\Asymptotics.lean',
        'Extension\Tao2026\Audit.lean',
        'Extension\Tao2026\BadIntervals.lean',
        'Extension\Tao2026\BadIntervalMaximal.lean',
        'Extension\Tao2026\NormalizedBadIntervals.lean',
        'Extension\Tao2026\TypicalBadIntervals.lean',
        'Extension\Tao2026\NonTypicalBadIntervals.lean',
        'Extension\Tao2026\BadIntervalSourceScales.lean',
        'Extension\Tao2026\BadIntervalLongSieve.lean',
        'Extension\Tao2026\BadIntervalCofactorSieve.lean',
        'Extension\Tao2026\BadIntervalLongOptimization.lean',
        'Extension\Tao2026\BadIntervalLongSaddle.lean',
        'Extension\Tao2026\BadIntervalLongSum.lean',
        'Extension\Tao2026\BadIntervalLargePrimeSum.lean',
        'Extension\Tao2026\BadIntervalSmoothBranches.lean',
        'Extension\Tao2026\BadIntervalLargeLength.lean',
        'Extension\Tao2026\BadIntervalProposition65.lean',
        'Extension\Tao2026\BadIntervalSlowCutoff.lean',
        'Extension\Tao2026\BadIntervalRandomModel.lean',
        'Extension\Tao2026\BadIntervalAntiSieve.lean',
        'Extension\Tao2026\BadIntervalSmallPrimeMoment.lean',
        'Extension\Tao2026\BadIntervalLargePrimeMoment.lean',
        'Extension\Tao2026\BadIntervalLargePrimeCharacter.lean',
        'Extension\Tao2026\BadIntervalPrincipalCharacter.lean',
        'Extension\Tao2026\BadIntervalLargePrimeNonprincipal.lean',
        'Extension\Tao2026\BadIntervalLargePrimeProductNonprincipal.lean',
        'Extension\Tao2026\BadIntervalLargePrimeProductCollision.lean',
        'Extension\Tao2026\BadIntervalLargePrimeCrude.lean',
        'Extension\Tao2026\BadIntervalPrimeTupleUniform.lean',
        'Extension\Tao2026\BadIntervalPrimeTupleFiber.lean',
        'Extension\Tao2026\BadIntervalPrimeTupleMultiFiber.lean',
        'Extension\Tao2026\BadIntervalLargePrimeCrudeNormalize.lean',
        'Extension\Tao2026\BadIntervalLargePrimeCrudeSource.lean',
        'Extension\Tao2026\BadIntervalLargePrimeProbabilityBounds.lean',
        'Extension\Tao2026\BadIntervalLargePrimeAggregation.lean',
        'Extension\Tao2026\BadIntervalLargePrimeExceptionalPartition.lean',
        'Extension\Tao2026\BadIntervalLargePrimeBlockSum.lean',
        'Extension\Tao2026\BadIntervalLargePrimeCovarianceBlockSum.lean',
        'Extension\Tao2026\BadIntervalLargePrimeExceptionalPairCard.lean',
        'Extension\Tao2026\BadIntervalLargePrimeErrorNormalize.lean',
        'Extension\Tao2026\BadIntervalLargePrimeErrorSource.lean',
        'Extension\Tao2026\BadIntervalLargePrimeErrorPower.lean',
        'Extension\Tao2026\BadIntervalLargePrimeAdaptiveExceptional.lean',
        'Extension\Tao2026\BadIntervalLargePrimeAdaptiveError.lean',
        'Extension\Tao2026\BadIntervalLargePrimeAdaptivePartition.lean',
        'Extension\Tao2026\BadIntervalLargePrimeAdaptiveBlockSum.lean',
        'Extension\Tao2026\BadIntervalLargePrimeAdaptiveSource.lean',
        'Extension\Tao2026\BadIntervalLargePrimeAdaptiveGeometry.lean',
        'Extension\Tao2026\BadIntervalLargePrimeAdaptiveComplete.lean',
        'Extension\Tao2026\BadIntervalLargePrimeDyadicScales.lean',
        'Extension\Tao2026\BadIntervalLargePrimeAdaptiveUniform.lean',
        'Extension\Tao2026\BadIntervalProbabilityNormalization.lean',
        'Extension\Tao2026\BadIntervalTypicalAntiSieve.lean',
        'Extension\Tao2026\BadIntervalProbabilityUniform.lean',
        'Extension\Tao2026\BadIntervalTypicalCounting.lean',
        'Extension\Tao2026\BadIntervalTypicalScales.lean',
        'Extension\Tao2026\BadIntervalTypicalEnlargement.lean',
        'Extension\Tao2026\BadIntervalTypicalMultiplicity.lean',
        'Extension\Tao2026\BadIntervalTypicalGlobal.lean',
        'Extension\Tao2026\BadIntervalTypicalAssembly.lean',
        'Extension\Tao2026\BadIntervalTypicalWeighted.lean',
        'Extension\Tao2026\BadIntervalTypicalUnion.lean',
        'Extension\Tao2026\BadIntervalBackwardSmallPrime.lean',
        'Extension\Tao2026\BadIntervalBackwardLargePrime.lean',
        'Extension\Tao2026\BadIntervalBackwardLargePrimeAdaptiveBlockSum.lean',
        'Extension\Tao2026\BadIntervalBackwardLargePrimeAdaptiveUniform.lean',
        'Extension\Tao2026\BadIntervalBackwardProbabilityNormalization.lean',
        'Extension\Tao2026\BadIntervalBackwardTypicalAntiSieve.lean',
        'Extension\Tao2026\BadIntervalBackwardTypicalWeighted.lean',
        'Extension\Tao2026\BadIntervalBackwardTypicalUnion.lean',
        'Extension\Tao2026\BadIntervalSlowCutoffLogSaving.lean',
        'Extension\Tao2026\BadIntervalRecombination.lean',
        'Extension\Tao2026\BadIntervalDyadicSummation.lean',
        'Extension\Tao2026\BadOneTermRegularVariation.lean',
        'Extension\Tao2026\BadIntervalLargePrimeExceptional.lean',
        'Extension\Tao2026\BadIntervalCharacterExpansion.lean',
        'Extension\Tao2026\PrimeCharacterSums.lean',
        'Extension\Tao2026\SmallPrimeMertens.lean',
        'Extension\Tao2026\ExceptionalCharacterBHM.lean',
        'Extension\Tao2026\FundamentalSieveWeights.lean',
        'Extension\Tao2026\SelbergPrimeWeights.lean',
        'Extension\Tao2026\ExceptionalCharacterSelberg.lean',
        'Extension\Tao2026\ExceptionalCharacterFamilies.lean',
        'Extension\Tao2026\ExceptionalCharacterBurgess.lean',
        'Extension\Tao2026\BurgessMoment.lean',
        'Extension\Tao2026\BurgessAmplification.lean',
        'Extension\Tao2026\BurgessWeilCRT.lean',
        'Extension\Tao2026\BurgessWeilIteration.lean',
        'Extension\Tao2026\BurgessWeilPrimeSquare.lean',
        'Extension\Tao2026\BurgessWeilPrime.lean',
        'Extension\Tao2026\BurgessWeilPrimePolynomial.lean',
        'Extension\Tao2026\BurgessWeilPrimeLowRoots.lean',
        'Extension\Tao2026\BurgessWeilPrimeActiveRoots.lean',
        'Extension\Tao2026\BurgessWeilPrimeThreeRoots.lean',
        'Extension\Tao2026\BurgessWeilPrimeLargeCharacteristic.lean',
        'Extension\Tao2026\BurgessWeilPrimeFourRoots.lean',
        'Extension\Tao2026\BurgessWeilPrimeSourceResidual.lean',
        'Extension\Tao2026\ExceptionalCharacterScales.lean',
        'Extension\Tao2026\ExceptionalCharacterNormalization.lean',
        'Extension\Tao2026\ExceptionalCharacterAbsorption.lean',
        'Extension\Tao2026\ExceptionalCharacterFixedLevel.lean',
        'Extension\Tao2026\ExceptionalCharacterAggregate.lean',
        'Extension\Tao2026\ExceptionalCharacterCofactorAggregate.lean',
        'Extension\Tao2026\ExceptionalCharacterUniformCard.lean',
        'Extension\Tao2026\ExceptionalCharacterCofactorUniform.lean',
        'Extension\Tao2026\BadIntervalLargePrimePairs.lean',
        'Extension\Tao2026\SmallPrimeExceptionalConductors.lean',
        'Extension\Tao2026\CoefficientBounds.lean',
        'Extension\Tao2026\CoefficientProduct.lean',
        'Extension\Tao2026\CoefficientSelection.lean',
        'Extension\Tao2026\ConvolutionRearrangement.lean',
        'Extension\Tao2026\Counting.lean',
        'Extension\Tao2026\CriticalIntervals.lean',
        'Extension\Tao2026\FactorialCoefficientBounds.lean',
        'Extension\Tao2026\FactorialEquidistribution.lean',
        'Extension\Tao2026\FactorialLowGeometry.lean',
        'Extension\Tao2026\FactorialAsymptotics.lean',
        'Extension\Tao2026\FactorialFibers.lean',
        'Extension\Tao2026\FactorialIntervals.lean',
        'Extension\Tao2026\FactorialOneTerm.lean',
        'Extension\Tao2026\FactorialOneTermAsymptotics.lean',
        'Extension\Tao2026\FactorialShortIntervals.lean',
        'Extension\Tao2026\Intervals.lean',
        'Extension\Tao2026\IntervalMultiples.lean',
        'Extension\Tao2026\PrimeIntervals.lean',
        'Extension\Tao2026\PrimeEquidistribution.lean',
        'Extension\Tao2026\PrimePowerReduction.lean',
        'Extension\Tao2026\PartialSummation.lean',
        'Extension\Tao2026\PhaseVariation.lean',
        'Extension\Tao2026\PowerfulAsymptotics.lean',
        'Extension\Tao2026\PowerfulExtraction.lean',
        'Extension\Tao2026\PowerfulLimit.lean',
        'Extension\Tao2026\PowerfulNumbers.lean',
          'Extension\Tao2026\PowerfulRelations.lean',
          'Extension\Tao2026\PowerfulRelationCounting.lean',
          'Extension\Tao2026\SquareRelations.lean',
          'Extension\Tao2026\QuadraticUnits.lean',
          'Extension\Tao2026\QuadraticIdealDivisors.lean',
          'Extension\Tao2026\QuadraticSolutionCount.lean',
          'Extension\Tao2026\PublicStatements.lean',
        'Extension\Tao2026\SmoothNumbers.lean',
        'Extension\Tao2026\SmoothNumberRankin.lean',
        'Extension\Tao2026\SmoothNumberPrimeSum.lean',
        'Extension\Tao2026\SmoothNumberSourceRegimes.lean',
        'Extension\Tao2026\SmoothNumberPolylogRegimes.lean',
        'Extension\Tao2026\SmoothNumberLowerBound.lean',
        'Extension\Tao2026\SmoothNumberHildebrand.lean',
        'Extension\Tao2026\SmoothNumberCriticalLower.lean',
        'Extension\Tao2026\SmoothNumberCEPPacket.lean',
        'Extension\Tao2026\SmoothNumberCEPRecurrence.lean',
        'Extension\Tao2026\SmoothNumberCEPIntervals.lean',
        'Extension\Tao2026\SmoothNumberCEPWeights.lean',
        'Extension\Tao2026\SmoothNumberCEPSource.lean',
        'Extension\Tao2026\SmoothNumberCEPSize.lean',
        'Extension\Tao2026\SmoothNumberCEPPrimeMass.lean',
        'Extension\Tao2026\SmoothNumberCEPBootstrap.lean',
        'Extension\Tao2026\SmoothNumberCEPCoarse.lean',
        'Extension\Tao2026\SmoothNumberSaddlePoint.lean',
        'Extension\Tao2026\SmoothNumberSaddleRegimes.lean',
        'Extension\Tao2026\SmoothNumberSaddlePhase.lean',
        'Extension\Tao2026\SmoothNumberSaddleTilt.lean',
        'Extension\Tao2026\SmoothNumberSaddleProbability.lean',
        'Extension\Tao2026\SmoothNumberSaddleEulerCharacteristic.lean',
        'Extension\Tao2026\SmoothNumberSaddleFrequency.lean',
        'Extension\Tao2026\SmoothNumberSaddleCentralWindow.lean',
        'Extension\Tao2026\SmoothNumberSaddleCurvatureLower.lean',
        'Extension\Tao2026\SmoothNumberSaddleGaussianProduct.lean',
        'Extension\Tao2026\SmoothNumberStability.lean',
        'Extension\Tao2026\SmoothNumberSaddleCurvature.lean',
        'Extension\Tao2026\SmoothNumberSaddleLocalLimit.lean',
        'Extension\Tao2026\BadOneTermAsymptotics.lean',
        'Extension\Tao2026\ShortIntervalDecomposition.lean',
        'Extension\Tao2026\TypeIReduction.lean',
        'Extension\Tao2026\TypeIIReduction.lean',
        'Extension\Tao2026\TypeIIKernel.lean',
        'Extension\Tao2026\VeryBadIntervals.lean',
        'Extension\Tao2026\VinogradovPhase.lean',
        'Extension\Tao2026\VaughanIdentity.lean',
        'Extension\Tao2026\WeylDifferencing.lean',
        'Sources\PINS.md',
        'Sources\SHA256SUMS.txt',
        'Sources\baker-harman-pintz-2001.pdf',
        'Sources\erdos-selfridge-1975.pdf',
        'Sources\granville-smooth-numbers-2008.pdf',
        'Sources\canfield-erdos-pomerance-1983.pdf',
        'Sources\burgess-character-sums-primitive-roots-1962.pdf',
        'Sources\explicit-burgess-cubefree-2511.17778v2.pdf',
        'Sources\explicit-burgess-cubefree-2511.17778v2.tar',
        'Sources\singmaster-2106.03335v1.pdf',
        'Sources\singmaster-2106.03335v1.tar',
        'Sources\tao-unusual-anatomy-2603.27990v2.pdf',
        'Sources\tao-unusual-anatomy-2603.27990v2.tar',
        'Tools\README.md',
        'Tools\refresh_gafnitao_snapshot.ps1',
        'Tools\run_tao_build.ps1',
        'run_tao_build.bat',
        'push_to_github.bat'
    )

    Write-Host 'Checking project inventory...'
    foreach ($relativePath in $requiredFiles) {
        $fullPath = Join-Path $nodeRoot $relativePath
        if (-not (Test-Path -LiteralPath $fullPath -PathType Leaf)) {
            throw "Missing required project file: $relativePath"
        }
    }

    Write-Host 'Checking raw Mermaid architecture...'
    $architectureLines = @(Get-Content -LiteralPath (Join-Path $nodeRoot 'Tao Architecture.md'))
    if ($architectureLines.Count -eq 0 -or $architectureLines[0] -ne 'flowchart TD') {
        throw 'Tao Architecture.md must begin with: flowchart TD'
    }
    if ($architectureLines | Where-Object { $_ -match '^\s*#' -or $_ -match '^\s*```' }) {
        throw 'Tao Architecture.md must remain raw Mermaid without Markdown headings or fences.'
    }

    Write-Host 'Checking pinned Tao source hashes...'
    $hashLines = @(
        Get-Content -LiteralPath (Join-Path $nodeRoot 'Sources\SHA256SUMS.txt') |
            Where-Object { $_.Trim() }
    )
    if ($hashLines.Count -ne 11) {
        throw 'SHA256SUMS.txt must contain exactly the Tao PDF and TeX archive, Baker-Harman-Pintz PDF, Erdos-Selfridge PDF, Granville and Canfield-Erdos-Pomerance smooth-number PDFs, Burgess 1962 PDF, explicit cubefree Burgess PDF and TeX archive, and Singmaster PDF and TeX archive.'
    }
    foreach ($line in $hashLines) {
        if ($line -notmatch '^([0-9A-Fa-f]{64})\s{2}(.+)$') {
            throw "Malformed SHA-256 manifest line: $line"
        }
        $expectedHash = $Matches[1].ToUpperInvariant()
        $sourceName = $Matches[2]
        $sourcePath = Join-Path (Join-Path $nodeRoot 'Sources') $sourceName
        if (-not (Test-Path -LiteralPath $sourcePath -PathType Leaf)) {
            throw "Pinned source is missing: $sourceName"
        }
        if ((Get-FileHash -LiteralPath $sourcePath -Algorithm SHA256).Hash -ne $expectedHash) {
            throw "SHA-256 mismatch for $sourceName"
        }
    }

    $frozenRoot = Join-Path $nodeRoot 'Dependencies\GafniTaoFrozen'
    Write-Host 'Checking frozen Gafni-Tao source closure...'
    $frozenHashLines = @(
        Get-Content -LiteralPath (Join-Path $frozenRoot 'SOURCE_SHA256SUMS.txt') |
            Where-Object { $_.Trim() }
    )
    if ($frozenHashLines.Count -ne 1339) {
        throw "Frozen source manifest must contain exactly 1339 modules; found $($frozenHashLines.Count)."
    }
    $manifestFiles = [System.Collections.Generic.HashSet[string]]::new(
        [System.StringComparer]::OrdinalIgnoreCase)
    $frozenPrefix = [System.IO.Path]::GetFullPath($frozenRoot).TrimEnd('\') + '\'
    foreach ($line in $frozenHashLines) {
        if ($line -notmatch '^([0-9A-Fa-f]{64})\s{2}(.+\.lean)$') {
            throw "Malformed frozen SHA-256 manifest line: $line"
        }
        $expectedHash = $Matches[1].ToUpperInvariant()
        $relativePath = $Matches[2].Replace('/', '\')
        $sourcePath = [System.IO.Path]::GetFullPath((Join-Path $frozenRoot $relativePath))
        if (-not $sourcePath.StartsWith($frozenPrefix,
                [System.StringComparison]::OrdinalIgnoreCase)) {
            throw "Frozen manifest path escapes dependency root: $relativePath"
        }
        if (-not $manifestFiles.Add($relativePath)) {
            throw "Duplicate frozen manifest entry: $relativePath"
        }
        if (-not (Test-Path -LiteralPath $sourcePath -PathType Leaf)) {
            throw "Frozen source is missing: $relativePath"
        }
        if ((Get-FileHash -LiteralPath $sourcePath -Algorithm SHA256).Hash -ne $expectedHash) {
            throw "Frozen source SHA-256 mismatch: $relativePath"
        }
    }
    $actualFrozenFiles = @(
        Get-ChildItem -LiteralPath $frozenRoot -Recurse -File -Filter '*.lean' |
            ForEach-Object { $_.FullName.Substring($frozenRoot.Length + 1) }
    )
    if ($actualFrozenFiles.Count -ne 1339) {
        throw "Frozen dependency must contain exactly 1339 Lean modules; found $($actualFrozenFiles.Count)."
    }
    foreach ($relativePath in $actualFrozenFiles) {
        if (-not $manifestFiles.Contains($relativePath)) {
            throw "Unmanifested frozen Lean source: $relativePath"
        }
    }

    Write-Host 'Checking Lean and Mathlib pins...'
    $toolchain = (Get-Content -LiteralPath (Join-Path $extensionRoot 'lean-toolchain') -Raw).Trim()
    if ($toolchain -ne 'leanprover/lean4:v4.30.0') {
        throw "Unexpected Lean toolchain: $toolchain"
    }
    $manifest = Get-Content -LiteralPath (Join-Path $extensionRoot 'lake-manifest.json') -Raw |
        ConvertFrom-Json
    $mathlib = @($manifest.packages | Where-Object { $_.name -eq 'mathlib' })
    if ($mathlib.Count -ne 1 -or
        $mathlib[0].rev -ne 'c5ea00351c28e24afc9f0f84379aa41082b1188f') {
        throw 'The resolved Mathlib dependency does not match the frozen commit.'
    }
    $frozenToolchain = (Get-Content -LiteralPath (Join-Path $frozenRoot 'lean-toolchain') -Raw).Trim()
    if ($frozenToolchain -ne 'leanprover/lean4:v4.30.0') {
        throw "Unexpected frozen dependency Lean toolchain: $frozenToolchain"
    }
    $frozenManifest = Get-Content -LiteralPath (Join-Path $frozenRoot 'lake-manifest.json') -Raw |
        ConvertFrom-Json
    $frozenMathlib = @($frozenManifest.packages | Where-Object { $_.name -eq 'mathlib' })
    if ($frozenMathlib.Count -ne 1 -or
        $frozenMathlib[0].rev -ne 'c5ea00351c28e24afc9f0f84379aa41082b1188f') {
        throw 'The frozen dependency Mathlib resolution does not match the frozen commit.'
    }
    $leanArchitect = @($frozenManifest.packages |
        Where-Object { $_.name -eq 'LeanArchitect' })
    if ($leanArchitect.Count -ne 1 -or
        $leanArchitect[0].rev -ne 'b72ae37b08d264cf371f164f4ba60c5257c17727') {
        throw 'The frozen dependency LeanArchitect resolution does not match its pin.'
    }

    Write-Host 'Checking production-root coverage and forbidden proof shortcuts...'
    $developmentOnlyLeanFiles = @('ProbeBase.lean', 'ProbeRam.lean')
    $leanFiles = @(
        Get-ChildItem -LiteralPath $extensionRoot -Recurse -File -Filter '*.lean' |
            Where-Object { $_.FullName -notmatch '[\\/]\.lake[\\/]' } |
            Where-Object {
                -not ($_.DirectoryName -eq $extensionRoot -and
                    $_.Name -in $developmentOnlyLeanFiles)
            }
    )
    $rootText = Get-Content -LiteralPath (Join-Path $extensionRoot 'Tao2026.lean') -Raw
    foreach ($source in $leanFiles) {
        if ($source.Name -eq 'Tao2026.lean') { continue }
        $relative = $source.FullName.Substring($extensionRoot.Length + 1)
        $module = $relative.Substring(0, $relative.Length - 5).Replace('\', '.')
        if ($rootText -notmatch "(?m)^import\s+$([regex]::Escape($module))\s*$") {
            throw "Production module is not imported directly by Tao2026.lean: $module"
        }
    }
    $forbiddenPattern = '(?m)(^\s*(axiom|constant)\s+|\bsorry\b|\badmit\b|\bnative_decide\b|\bimplemented_by\b|^\s*unsafe\s+)'
    foreach ($source in Get-ChildItem -LiteralPath $frozenRoot -Recurse -File -Filter '*.lean') {
        $matches = Select-String -LiteralPath $source.FullName -Pattern $forbiddenPattern
        if ($matches) {
            $first = $matches | Select-Object -First 1
            throw "Forbidden proof shortcut in frozen dependency $($source.FullName):$($first.LineNumber)"
        }
    }
    foreach ($source in $leanFiles) {
        $matches = Select-String -LiteralPath $source.FullName -Pattern $forbiddenPattern
        if ($matches) {
            $first = $matches | Select-Object -First 1
            throw "Forbidden proof shortcut in $($source.Name):$($first.LineNumber)"
        }
    }

    $elanRoot = if ($env:ELAN_HOME) { $env:ELAN_HOME } else { Join-Path $env:USERPROFILE '.elan' }
    if (-not $env:ELAN_HOME) { $env:ELAN_HOME = $elanRoot }
    $lakeExecutable = Join-Path $elanRoot 'bin\lake.exe'
    if (-not (Test-Path -LiteralPath $lakeExecutable -PathType Leaf)) {
        $lakeCommand = Get-Command lake -ErrorAction SilentlyContinue
        $lakeExecutable = if ($lakeCommand) { $lakeCommand.Source } else { $null }
    }
    if (-not $lakeExecutable) {
        throw 'Unable to locate lake. Install elan/Lean or add lake to PATH.'
    }

    Write-Host 'Building the isolated Tao2026 production root...'
    Push-Location $extensionRoot
    try {
        $buildOutput = @(& $lakeExecutable build Tao2026 2>&1)
        $lakeExit = $LASTEXITCODE
    }
    finally {
        Pop-Location
    }
    $buildOutput | ForEach-Object { Write-Host $_ }
    if ($lakeExit -ne 0) {
        throw "lake build Tao2026 failed with exit code $lakeExit"
    }
    if ($buildOutput | Where-Object {
        $_ -match '(?i)(^|:\d+:\d+:\s*)warning:' -or
        $_ -match '(?i)declaration uses.+sorry'
    }) {
        throw 'The canonical Tao2026 build emitted a warning or tactic diagnostic.'
    }

    Write-Host 'MILESTONE: the full corrected Lemma 3.1 contract is closed conditional on Theorem 2.5: (N,H)=(0,1) is the unique exception to H<N, the all-start sufficiently-large-length Sylvester--Schur tail (with an explicit fixed-length start threshold and finite-rectangle reduction), unconditional eventual quadratic-window scale and H/400 measure lower bound, the complete fixed-constant logarithmic contradiction, and every fixed-slack subexponential bound are verified.'

    Write-Host 'MILESTONE: full Theorem 1.8 is unconditional. The source-faithful effective-degree Vinogradov argument and native quantitative PNT prove the exact specialized Theorem 2.5 contract; the finite nontrivial-value cover, injective Lemma 3.2 certificate/length/offset encoding, subpolynomial budgets, x^(2/5+o(1)) bound, and zeta-ratio asymptotic then prove TaoTheorem18Conclusion.'

    Write-Host 'MILESTONE: the remaining public Section 4 endpoints now expose exactly one premise. Proposition 2.3(ii) alone implies both TaoTheorem19Conclusion and TaoTheorem110Conclusion; source-facing variants require only the pinned Baker--Harman--Pintz proposition.'

    Write-Host 'MILESTONE: complete Lemma 4.1 (H<N and a<<H log N with one uniform constant), prime-freeness of every F3 interval, its exact triple tail-gap form, and the conditional public Theorem 1.10 asymptotic closure, verified.'

    Write-Host 'MILESTONE: full Lemma 4.2 at P=H log^2 N is closed conditional on Theorem 2.5 and the exact Proposition 2.3(ii) interface: both high- and low-P cutoffs, zero sums, O(log^12 N) C3 control, geometric and integral lower bounds, final contradictions, and the low/high case split are verified; the source-shaped backward BHP theorem is also proved to imply the exact Tao interface, including endpoint and finite-range transfer; Lemma 4.2 is propagated to Theorem 1.10 through an explicit ceiling gap budget proved to be x^o(1), including bounded middle indices.'

    Write-Host 'MILESTONE: Lemma 4.3 is complete: canonical square extraction, prime support up to P=max(a,H), exact divisibility by the product envelope prod_{p<=P} p^(H/p+1), its O(H log P+P) logarithmic bound, two-half coefficient selection, and the final bounded smooth square relation c1*n1^2+h=c2*n2^2 with 0<h<H are verified.'

    Write-Host 'MILESTONE: the Theorem 1.9 counting closure is compiled. The bounded-H, small-a, and complementary residue-sieve branches are complete; finite Corollaries 2.8-2.9, the maximal-k specialization, nonempty-fiber reassembly, and absorption of the Lemma 4.1-4.2 budgets prove the nontrivial x^(1/2+o(1)) bound. Exponential growth of s(a!) and an O(log x)*sqrt(x) representation cover prove the one-term upper bound, while the square family supplies the lower bound. The exact TaoTheorem19Conclusion follows from Lemma 4.2 and is reduced to Theorem 2.5 plus Proposition 2.3(ii), or the pinned BHP source contract.'

    Write-Host 'MILESTONE: the Section 6 arithmetic core of Lemma 6.1 is compiled. Every non-singleton bad interval satisfies H<=N and is prime-free unconditionally. A local prime p0>H gives one interval term p0^2*m with smooth cofactor and p0-smoothness of every interval term. The large-length tail plus fixed-length thresholds yield one common start cutoff, and admissible starts eventually cross it at every dyadic scale. Admissible witnesses retain the exact natural bounds N<x<=4N+1 and p0^2*m<=2x.'

    Write-Host 'MILESTONE: the corrected exact core of Lemma 6.2 is compiled. Every admissible interval contains a bad power-of-two endpoint subinterval with the same p0^2*m witness, length H/4<Hprime<=H, and exact scale bounds x<=4Nprime+1 and Nprime+Hprime<=2x. The source same-window admissibility sentence is not assumed, since containment alone does not preserve intersection with [x/2,x].'

    Write-Host 'MILESTONE: the full corrected finite maximal-function transfer after Lemma 6.2 is compiled. Bounded admissible and comparable-scale normalized families and their unions are explicit; every admissible-union point lies in a four-length enlargement with normalized-union density at least 1/10. A greedy disjoint interval selection proves the finite uncentered weak-(1,1) inequality and the final cardinality bound #admissibleUnion<=30*#normalizedUnion.'

    Write-Host 'MILESTONE: the exact finite Definitions 6.3-6.4 typical/non-typical contracts are compiled with explicit asymptotic cutoffs. The ordered 1000-prime anatomy, smooth remainder, p0<squareThreshold consequence, and mprime<=2x/(p0^2*product) bound are verified. Conversely, at least 1000 multiplicity-counted cofactor prime factors above the lower cutoff construct the ordered anatomy by selecting the largest factors and leave a remainder smooth below the last; thus a remaining condition-(iii) failure has fewer than 1000 such factors. Canonical deficient packets generate an exact finite product/remainder cover, and the actual short square-avoiding condition-(iii) union is reduced to 4L*sum_p0 sum_a Psi((2x/p0^2)/a,y), over products a of fewer than 1000 admissible large primes. The condition-(ii) failure branch of Proposition 6.5 has an explicit finite large-square cover, exact floor-sum count, telescoping reciprocal-square tail, literal cutoffs L=ceil(log(x)^20) and D=ceil(z(x)^3), and the source weak bound #union<=24x/z(x)^(5/2) for the actual short normalized failure union, giving delta=1/2.'
    Write-Host 'MILESTONE: the deficient-product index has a literal finite expansion into multiplicity-retaining admissible factor lists of length below 1000, and the distinct-product Psi sum is bounded by this list sum for the next reciprocal-prime estimate.'
    Write-Host 'MILESTONE: the deficient condition-(iii) branch is quantitatively disposed of on its actual central interval union z(x)^(9/10)<p0<=z(x)^(11/10), as well as the high source subrange. At y=floor(z(x)^(9/10)), selector diagonalization is uniform in p0 and every fewer-than-1000 factor list, preserves the exact reciprocal weight 1/(p0^2*product), and combines with the reciprocal-square tail plus the elementary harmonic list-mass bound. The complete fixed logarithmic loss is absorbed, yielding #union<=x/z(x)^(2+1/200) eventually.'
    Write-Host 'MILESTONE: both fixed outside-central smooth-prime gaps are quantitatively closed on actual short normalized interval unions. A 600-cell exponent mesh covers z(x)^(2/5)<p0<=z(x)^(9/10) and z(x)^(11/10)<p0<=z(x)^(5/4); exact rounded-cutoff transfer to the cofactor scale 2x, finite dyadic aggregation, and arbitrary fixed logarithmic absorption give #union<=x/z(x)^(2+1/1000) eventually.'
    Write-Host 'MILESTONE: the complete fixed-cutoff Proposition 6.5 assembly is compiled. The actual non-typical normalized family at the concrete 9/10 and 11/10 window is contained exhaustively in eight named failure unions. The two fixed-power estimates are converted through log(z)/log(x)->0, every branch is normalized to one common z-saving, and the finite factor eight is absorbed, yielding #union<=x/z(x)^(2+1/4000) eventually.'
    Write-Host 'MILESTONE: the source-facing Proposition 6.5 slow-cutoff diagonal is compiled. For row d=n+10, the exact lower floor z(x)^(1-2/d) and upper ceiling z(x)^(1+2/d) are controlled by moving low/high meshes and the full intervening deficient range, giving an eight-branch bound #union<=x/z(x)^(2+1/(128d^2)). A countable diagonal selects q(x)->infinity; both rounded cutoff logarithms have ratio one to log z(x), and the selected actual non-typical union is eventually at most x/z(x)^2.'
    Write-Host 'MILESTONE: Proposition 6.6 now has a literal finite probability model. The 1001 coordinate projections carry exact uniform laws on the half-open dyadic prime bands, belong to those bands almost surely, and are mutually independent under the product measure. The source tuple product p0^2*p1*...*p1000*mprime, its divisibility indicators, the typical-interval event, and its probability are explicit production definitions; the anti-sieve moment estimate remains.'
    Write-Host 'MILESTONE: the exceptional-prime branch of Proposition 6.6 is closed pointwise. The complete p|l logarithmic weight is at most H*log(H), hence eventually at most H*log(z(x)) uniformly for every source-admissible H; its large event is empty and has exactly zero probability under every prime-tuple law. The small-prime branch uses the literal floor(z(x)^(1/100)) cutoff, removes p|l, retains moment 50, and expands exactly over ordered tuples. Each joint event is empty or one primitive residue fiber modulo its lcm. Character orthogonality, independent dyadic-average factorization, norm-one disposal, and weak AM-GM give 1000th powers. The exact lcm<=2^50*phi(lcm) comparison supplies coefficient 2^50/lcm; the bound is inserted into the full fiftieth moment, reordered by coordinate, and pigeonholed with factor 1000. Section 5 normalized sums use exact threshold Z^(-1/125). Scale separation justifies exact primitive-character replacement; the principal term is one; nonprincipal terms are regrouped by positive conductor; and the full ambient moment is bounded by a divisor sum of exceptional squares plus phi(d)*Z^(-8). This conductor estimate is inserted termwise into the ordered tuple expression and hence into the complete fiftieth moment. The tuple lcm is exactly the product of its distinct-prime support; multiplicities sum to 50 and split the coefficient into one log(p)/p per support prime plus repeated logarithms of total exponent 50-#support. Fixed ordered prime tuples have at most H^50 compatible shifts. Exact support regrouping, a 50^50 support-fiber bound, the elementary-symmetric inequality, and weighted Mertens sum every equality pattern, giving H^50*O(log(cutoff)^50). The conductor expression splits exactly into principal, exceptional-square, and totient-error parts; the principal and totient-error parts are bounded explicitly using the totient-divisor identity and Chebyshev theta. Applying the Burgess-conditional Lemma 5.1 family theorem to the isolated exceptional sum, plus the large-prime mean/variance bounds, remain.'
    Write-Host 'MILESTONE: the large-prime probability layer for Proposition 6.6 is exact. The literal unweighted contribution over 1<=l<H and the prescribed prime interval has finite mean, second-moment, variance, and double-covariance formulas. When H is below the prime cutoff, distinct shifts carrying the same prime have empty joint event and nonpositive covariance; the diagonal costs at most the mean, leaving only ordered distinct-prime covariances. The analytic estimates of Propositions 6.7--6.8 remain.'
    Write-Host 'MILESTONE: the character-algebra entry to Propositions 6.7--6.8 is compiled. Every single large-prime event is empty or one primitive residue fiber modulo p; every joint event for distinct primes is empty or one primitive fiber modulo ppprime. The literal single and joint probabilities are bounded by the existing all-character 1000th-moment expression at those exact moduli. Exceptional-prime and exceptional-pair analytic counting remains.'
    Write-Host 'MILESTONE: the exceptional p and ppprime counting layer of Propositions 6.7--6.8 is closed conditional on analytic Burgess. Exceptional prime conductors are bounded by the aggregate Lemma 5.1 character count with exponent 2/125. For products ppprime, a dependent common-factor family retains p and varies pprime. The self-improving cardinal proof has one family-independent constant, selector diagonalization makes it pointwise uniform in p, and the exact prime-partner specialization again gives exponent 2/125. Probability errors, crude estimates, and dyadic aggregation remain.'
    Write-Host 'MILESTONE: the principal-character collision layer of Propositions 6.7--6.8 is compiled. The unique principal character is separated before weak AM-GM, so the main term is charged once. Its tuple expectation equals the exact coprimality probability. If mprime is coprime to p or ppprime, every principal loss forces a sampled-coordinate collision; uniform dyadic laws and primality bound each coordinate by one reciprocal exact band cardinality. Finite union bounds give one copy for p and two copies for ppprime. Nonprincipal improved errors, crude fallback estimates, and dyadic aggregation remain.'
    Write-Host 'MILESTONE: the one-prime nonprincipal improved-error layer of Proposition 6.7 is compiled. Every nonprincipal character modulo a prime is primitive. Outside the union of exceptional conductors over the 1000 ordinary coordinate scales, the complete nonprincipal moment is at most phi(p) times the sum of Pj^(-8). The exceptional union cardinal is at most the sum of its coordinate cardinalities, hence costs only the fixed factor 1000 under a uniform bound. Substitution into the principal collision estimate gives a direct deviation from 1/phi(p). The two-prime conductor split, crude estimates, and dyadic aggregation remain.'
    Write-Host 'MILESTONE: the product-modulus conductor reduction of Proposition 6.8 is compiled under exact band separation. Ambient nonprincipal characters are regrouped by their primitive nontrivial divisor conductors; if all are unexceptional, the totient divisor identity bounds the full moment by q*Z^(-8). For q=ppprime this sums to ppprime times the coordinate Z^(-8) errors and feeds the direct deviation estimate. Removing the band-separation hypothesis by charging possible p or pprime sample points to collision error remains, together with crude estimates and dyadic aggregation.'
    Write-Host 'MILESTONE: the Proposition 6.8 change-level collision boundary is removed. An ambient character modulo ppprime differs from its primitive counterpart on at most the two sampled band points p and pprime, giving norm error at most four divided by the exact band cardinality. A coprimality-free primitive conductor regrouping, totient cardinal bound, and 1000th-power convexity yield the full ambient nonprincipal moment with an explicit (4/card)^1000 correction. The direct deviation from 1/phi(ppprime) now has no band-separation hypothesis. Crude fallback estimates and dyadic aggregation remain.'
    Write-Host 'MILESTONE: the first exact finite counting input for the crude parts of Propositions 6.7--6.8 is compiled. The primes in [Z,2Z) occupying one residue class modulo positive q form a literal finset of cardinality at most floor(2Z/q)+1, proved from the exact interval residue count. Its normalized real form is available for the forthcoming frozen-coordinate probability estimate.'
    Write-Host 'MILESTONE: the finite product probability law is converted to exact tuple counting for the crude estimates. Its literal Cartesian support has measure one; every supported 1001-prime tuple has atom mass equal to the inverse product of the exact dyadic-band cardinalities; and every event probability equals its supported tuple cardinality times this common atom. This is the rigorous finite replacement for source-level informal conditioning when freezing coordinates.'
    Write-Host 'MILESTONE: the frozen-coordinate crude probability bridge is compiled. Replacing one ordinary coordinate by zero gives an exact 1000-coordinate support whose cardinality times the missing band cardinality is the full support cardinality. Uniform event-fiber cardinal bounds therefore divide by the exact missing-band size. Pairwise residue rigidity invokes the elementary floor(2P/q)+1 progression count, and the source product is factored as a coordinate times its complementary cofactor. Splitting into coprime and noncoprime source products and applying the proved coordinate-collision unions removes the cofactor premise: single-p probability is bounded by the crude ratio plus one collision sum, and joint-ppprime probability by the crude ratio plus two collision sums. Dyadic aggregation remains.'
    Write-Host 'MILESTONE: the source coordinate-freezing arguments for the crude parts of Propositions 6.7(i) and 6.8(i) are compiled in exact finite form. Arbitrary finite coordinate sets have an exact support-cardinality cancellation law and a general product-residue probability bound. Two prime coordinates represent a fixed product at most twice, and three at most six times. Freezing two coordinates yields the literal single-prime ratio 2*(floor(4Pj1Pj2/p)+1)/(cardBandj1*cardBandj2); freezing three yields the joint ratio 6*(floor(8Pj1Pj2Pj3/(ppprime))+1)/(cardBandj1*cardBandj2*cardBandj3). The event coprimality hypotheses are discharged from the nonzero shifts. Source-scale normalization and dyadic aggregation remain.'
    Write-Host 'MILESTONE: the exact crude fiber ratios are normalized to the source logarithmic shape. If every selected band satisfies Pj<=L*cardBandj, the two-coordinate theorem gives probability at most 16*L^2/p and the three-coordinate joint theorem gives at most 96*L^3/(ppprime), with the floor-plus-one term absorbed under the explicit modulus-below-product hypothesis. Instantiating the common L from the Pj=z^(1+o(1)) PNT contract and dyadic aggregation remain.'
    Write-Host 'MILESTONE: the Pj=z^(1+o(1)) source-scale specialization of the crude estimates is compiled. A precise 1001-coordinate scale contract records divergence and log(Pj)/log(z)->1. The dyadic PNT yields Pj<=4*log(z)*cardBandj simultaneously for every coordinate, and Bertrand gives simultaneous band nonemptiness. Consequently Proposition 6.7(i) has the explicit eventual bound 256*log(z)^2/p and Proposition 6.8(i) the bound 6144*log(z)^3/(ppprime), subject only to their exact eventual modulus-product comparisons. Dyadic mean/covariance aggregation remains.'
    Write-Host 'MILESTONE: the improved character estimates of Propositions 6.7(ii) and 6.8(ii) now reach the literal divisibility probabilities. Coprimality rules out the empty single-event branch and yields the absolute 1/phi(p) error; upper bounds retain empty-event cases; and exact phi(ppprime)=phi(p)phi(pprime) cancellation plus an audited real-algebra lemma gives the explicit distinct-prime covariance error. Finite dyadic aggregation remains.'
    Write-Host 'MILESTONE: the finite anti-sieve aggregation of Propositions 6.7 and 6.8 is compiled. The literal shift-prime index set is partitioned into improved and exceptional single conductors, while the ordered distinct-prime covariance sum is partitioned into improved and exceptional pairs. The diagonal variance reduction is combined with both partitions, preserving every shift multiplicity and exposing only supplied crude majorants on the exceptional pieces. Analytic cardinality and source-scale summation remain.'
    Write-Host 'MILESTONE: exceptional product pairs are reduced to the previously counted prime and common-factor families. For distinct primes the nontrivial divisors of ppprime are exactly p, pprime, and ppprime. Hence failure of product-modulus unexceptionality is covered by an exceptional p, an exceptional pprime, or membership of pprime in the common-factor exceptional-partner union over the 1000 coordinate scales; the latter union has the exact sum-cardinality and factor-1000 bounds. Weighted source-scale summation remains.'
    Write-Host 'MILESTONE: the finite dyadic first-moment block of Proposition 6.7 is compiled. The general anti-sieve range (R-1,2R-1] is identified exactly with the source half-open prime band [R,2R); 1/phi(p)<=2/R on that band; PNT gives the eventual main sum at most 4/log R; and the full shift-prime probability sum is bounded by (H-1) times the PNT main contribution, the uniform improved error over the whole band, and the exceptional-cardinality times a supplied crude bound. Source-scale normalization of the two error terms remains.'
    Write-Host 'MILESTONE: the exact finite two-band covariance block of Proposition 6.8 is compiled. Ordered distinct-prime covariances over dyadic bands R and S are bounded with the literal (H-1)^2 shift multiplicity by the whole band-product cardinality times a uniform improved error plus the exceptional ordered modulus-pair cardinality times a supplied crude joint bound. Source-scale normalization and dyadic scale summation remain.'
    Write-Host 'MILESTONE: the exact exceptional ordered modulus-pair count is reduced to the three source families. For any ambient conductor range containing both dyadic bands, its cardinality is bounded by exceptional first endpoints times the second band, exceptional second endpoints times the first band, and the sum of common-factor exceptional-partner counts; a real-valued uniform interface is compiled for Burgess insertion.'
    Write-Host 'MILESTONE: the improved one-prime, joint, and covariance errors now have explicit source-scale envelopes. The reciprocal coordinate-band mass, nonprincipal eighth-power tail, and 1000th-power change-level collision tail are each bounded uniformly from P_j=z^(1+o(1)) and PNT, then inserted into the literal dyadic error formulas. Power-form simplification, Burgess cardinality insertion, and dyadic scale summation remain.'
    Write-Host 'MILESTONE: the source improved-error envelopes are normalized to the exact power forms used in Propositions 6.7--6.8. Fixed logarithmic powers are absorbed by z-power savings, source-range dyadic selectors convert these to the uniform one-prime bound 3*R^(-1.001), and the joint and ordered covariance errors are bounded by explicit constants times R^(-1.001)*S^(-1). These estimates are also composed directly with the literal probability and covariance errors. Burgess cardinality insertion and finite dyadic scale summation remain.'
    Write-Host 'MILESTONE: the endpoint exceptional-conductor count now uses the scale-adaptive threshold max(P_j^(-0.008),R^(-0.01)) required across Tao''s full modulus range. The maximum stays inside the fixed exceptional family controlled by the uniform Lemma 5.1 squared moment, while finite Chebyshev and the union over 1000 ordinary coordinates give one Burgess-conditional bound O(R^0.02). This repairs the exponent mismatch of attempting to rewrite the fixed O(P_j^0.016) count at the smallest R.'
    Write-Host 'MILESTONE: the scale-adaptive exceptional-partner count is compiled with the source quantifier order. The cofactor embedding now preserves the complete squared moment exactly; one eventual moment constant is pointwise uniform in the fixed prime and cofactor set; and the threshold max(P_j^(-0.008),S^(-0.01)) plus finite Chebyshev gives O(S^0.02) partners uniformly in the fixed prime and ambient range. Adaptive finite-block partitions and summation remain.'
    Write-Host 'MILESTONE: Lemma 5.3 is proved in exact finite weighted form. Hermitian Gram symmetry gives the row-only Bombieri--Halasz--Montgomery inequality; a sieve weight equal to one on the dyadic prime band recovers the literal prime sum and band-cardinality energy; and each Gram row is split into one diagonal plus J-1 uniform off-diagonal terms. The later Selberg alternative supplies the needed diagonal input; analytic Burgess remains.'
    Write-Host 'MILESTONE: the Lemma 5.3 output is normalized by the exact dyadic-prime cardinality and identified definitionally with s_Z. The exact exceptional threshold square is Z^(-2/125), and finite Markov gives J*Z^(-2/125)<=sum |s_Z|^2. Thus a bounded exceptional squared moment yields Tao''s J<<Z^0.016 consequence with no decimal rounding.'
    Write-Host 'MILESTONE: the finite algebra around Lemma 5.4 is compiled. The truncated divisor-sum weight is literal; lambda_1=1 makes it exactly one on every dyadic prime above the sieve level; its mass on 1<=n<=X is exactly sum_{d<=R} floor(X/d)lambda_d; coefficient l1 mass is at most R when |lambda_d|<=1; and the floor replacement has exact error at most R, transferring any main-mass bound B to sum nu<=XB+R. Constructing coefficients with squarefree support, nonnegative weight, and O(1/log R) main mass remains the genuine fundamental-lemma input.'
    Write-Host 'MILESTONE: an unconditional real-valued Selberg alternative to the Rosser weights is compiled. Its coefficients are supported at d<=R and on the primorial, lambda_1=1, and the upper-Moebius property makes the literal divisor weight nonnegative and one on primes above R. Selberg diagonalization gives main mass<=2/log R; |lambda_d|<=3^omega(d) gives exact floor error<=R(1+log R)^3; hence sum_{n<=X}nu(n)<=2X/log R+R(1+log R)^3. The source-exact {-1,0,1} Rosser construction remains open.'
    Write-Host 'MILESTONE: the concrete Selberg weight is connected end-to-end to normalized finite BHM. The zero coordinate is removed exactly; weighted correlations expand over supported divisors; multiples are reindexed as ordinary prefixes m<=floor((2Z-1)/d); multiplicativity extracts the d-value at norm cost at most one; the diagonal uses the explicit Selberg mass; and the final normalized second-moment theorem leaves only the unshifted off-diagonal prefix bound supplied by Burgess.'
    Write-Host 'MILESTONE: Tao heterogeneous exceptional-character family bookkeeping is compiled. Primitive levels q1*q2 carry the stated coprimality, squarefreeness, and square-root bound; pair lcms equal q1*lcm(q2j,q2k), remain squarefree, and are at most Z^3.09. The raw conjugated correlation is exactly one quotient Dirichlet character on every natural input, including nonunits, and the complete normalized family BHM estimate is reduced to one explicit cubefree Burgess prefix-bound predicate.'
    Write-Host 'MILESTONE: the Burgess boundary for Lemma 5.1 is source-faithful and scale-complete. The exact sieve-prefix predicate only requests H=floor((2Z-1)/d); a proposition-valued explicit cubefree Burgess target uses saving 0.0163 and range q<=H^3.1. Cubefree is defined literally, squarefree consumer periods are proved cubefree, and the cited r=7 estimate A*H^(6/7)*q^(2/49+epsilon) with epsilon=1/2000000 is proved by exact exponent arithmetic to imply the decimal target. Changed-level prefixes are exactly Mobius-expanded into primitive prefixes of lengths H/d; the frozen divisor-epsilon bound absorbs the divisor count after splitting epsilon in half. Complete nonprincipal periods sum to zero, every primitive prefix equals its H mod q prefix, and the exact trivial bound handles the complementary lower range. Thus at epsilon=1/4000000 it suffices to prove the primitive cubefree estimate only for q^(2/7+7epsilon)<H<q. For canonical R=floor(Z^0.0001), complementary floor scales have product at most Z, every prefix eventually exceeds any fixed Burgess cutoff, Z^3.09 is eventually at most H^3.1 uniformly over supported divisors, and Bertrand discharges prime-band nonemptiness. The primitive analytic r=7 core therefore feeds the finite normalized family estimate with no remaining arithmetic or scale hypotheses.'
    Write-Host 'MILESTONE: the finite Burgess moment front end is compiled. The complete shifted 2r-moment expands exactly over ordered pairs of r-tuples and each term is rewritten as one complete quotient-character correlation, including nonunits. Degenerate tuples use at most r shifts; an injective code by r values and 2r labels proves cardinality at most r^(2r)B^r. The triangle inequality and trivial modulus bound yield moment<=r^(2r)B^r*q+B^(2r)W, with a literal r=7 fourteenth-moment specialization.'
    Write-Host 'MILESTONE: the pinned composite Burgess coefficient boundary is literal. Tagged shifts define A_j=product over i!=j of (b_i-b_j). Exact summation of value-fiber cardinalities proves that every nondegenerate 2r-tuple has a uniquely occurring shift and hence some nonzero A_j. The relaxed sum over gcd(abs(A_j),q), its trivial pointwise bound, the (4r)^omega(q)*sqrt(q) factor, and a proposition-valued primitive cubefree composite Weil interface compile. That interface feeds both the general complete moment and the exact r=7 fourteenth moment.'
    Write-Host 'MILESTONE: the finite Burgess gcd-weight sum is proved. Divisor-multiple counting gives sum_(n<=H) gcd(n,q)<=H*tau(q); centered splitting, gcd submultiplicativity for A_j, and exact independent-coordinate factorization give sum_uv weight<=2r*B*(2B*tau(q))^(2r-1). Checked general and r=7 moment consumers incorporate this bound. The composite complete Weil predicate is the only remaining input in the moment stage.'
    Write-Host 'MILESTONE: the r=7 Burgess moment is in source analytic form. The frozen fixed-base prime-factor estimate absorbs 28^omega(q), the divisor-epsilon estimate absorbs tau(q)^13, and an even epsilon split gives moment<=7^14*B^7*q+C_epsilon*B^14*q^(1/2+epsilon) for every positive epsilon, conditional only on the composite Weil predicate.'
    Write-Host 'MILESTONE: the composite Weil CRT layer is compiled. Canonical characters on two coprime factors multiply exactly to the global character; tuple numerators and denominators commute with both CRT projections; and the complete quotient correlation factors into the two local correlations. The factor (4r)^omega(q)*sqrt(q) and every fixed gcd(abs(A_j),q) contribution are multiplicative. Hence two local estimates with one common coefficient witness assemble into the relaxed global gcd-weight estimate. Local primitivity, cube-free iteration, and the prime and prime-square Weil bounds remain.'
    Write-Host 'MILESTONE: primitivity descends through the canonical Burgess CRT characters. The global character equals the product of the two local characters changed back to level mn. A factorization of the left local character through d gives a global factorization through dn, and symmetrically on the right. For a primitive global character, conductor divisibility and cancellation force both local conductors to equal their full levels. Cube-free iteration and the local prime and prime-square Weil estimates remain.'
    Write-Host 'MILESTONE: cube-free iteration of the complete Weil estimate is compiled. Every nontrivial cube-free modulus has a least-prime-factor split p^k*n with k equal to 1 or 2, coprime factors, and n strictly smaller. Strong induction preserves one fixed nonzero A_j through the exact CRT factorization and primitive local characters. Selecting a nonzero coefficient for each nondegenerate tuple and inserting it into the relaxed gcd weight proves the full composite Weil predicate from only the primitive fixed-coefficient estimates modulo p and p^2.'
    Write-Host 'MILESTONE: the local Burgess coefficient dichotomy is compiled. If p divides abs(A_j), the trivial modulus bound is dominated by the fixed-gcd target at both p and p^2. Therefore only gcd(abs(A_j),p)=1 remains analytic. Separate primitive prime and prime-square predicates are stated, and their conjunction is proved to imply the local prime-power predicate and the full relaxed composite Weil predicate.'
    Write-Host 'MILESTONE: the primitive prime-square Burgess Weil estimate is complete. The correlation modulo p^2 is decomposed into base-p fibers; singular fibers vanish; and restriction to 1+pt gives a nontrivial additive character. Exact first-order product identities give frequency F''/F-G''/G and cancel every nonstationary fiber. Coprimality of A_j makes F''G-FG'' nonzero at its tagged simple root, so at most 2r fibers survive and the local norm is at most 4rp. Only the primitive prime-modulus Weil estimate remains in the composite complete-sum boundary.'
    Write-Host 'MILESTONE: the sole prime-modulus Burgess boundary is normalized to a finite-field theorem. The complete correlation is exactly the sum of a nontrivial multiplicative character on one product of linear factors times the inverse character on another. Coprimality of A_j makes its tagged reduced shift unique, and primitivity at prime level makes the character nontrivial. Therefore the general bound 4r*sqrt(p) for this uniquely rooted linear quotient implies the primitive prime estimate and, using the completed prime-square and CRT layers, the full cube-free composite Weil predicate. The finite-field Weil theorem itself remains analytic input.'
    Write-Host 'MILESTONE: the prime finite-field boundary is reduced to the standard split-polynomial Weil form. Raising the denominator product to orderOf(chi)-1 preserves every character value, so the quotient sum is exactly one polynomial character sum. At the uniquely tagged root, exact root-multiplicity calculations give 1 on the numerator side or orderOf(chi)-1 on the denominator side; hence the polynomial is not an orderOf(chi)-th power. It splits and has at most 2r distinct roots. Thus a split-polynomial character bound by twice the distinct-root count times sqrt(p) implies the complete composite Weil predicate. That classical Weil bound remains open.'
    Write-Host 'MILESTONE: the one- and two-root split-polynomial Weil cases are complete. Split evaluation groups the root multiset by multiplicity. A single nontrivial root exponent gives a translated complete nontrivial-character sum and vanishes. Two roots reduce by an exact affine reindexing to a Jacobi sum; Mathlib Gauss-sum identities give norm at most sqrt(p), including trivial and inverse-product edge cases. Hence the sole prime input may be restricted to split polynomials with at least three distinct roots.'
    Write-Host 'MILESTONE: the prime Weil boundary for the cleared Burgess polynomial is reduced further to at least four active roots. Exact degree r*orderOf(chi) makes the active multiplicity sum divisible by the character order. With exactly three active roots, a verified Mobius equivalence sends one root to infinity, cancels the denominator character, and leaves a two-root Jacobi sum with one deleted point; the resulting sqrt(p)+1 bound and inactive-root correction are absorbed by the existing 2*#roots*sqrt(p) allowance.'
    Write-Host 'MILESTONE: small prime characteristics are removed from the Burgess Weil boundary. Every complete polynomial-character sum has norm at most p, which is already at most 2*D*sqrt(p) when p<=4*D^2 and D is the distinct-root count. The remaining degree-divisible, four-active-root input may therefore assume 4*D^2<p.'
    Write-Host 'MILESTONE: the exactly-four-active-root Burgess boundary is normalized to a canonical three-point hypergeometric sum. A fractional-linear permutation sends one root to infinity, degree divisibility cancels the denominator character, and the deleted point costs one. A canonical 2*sqrt(p) estimate proves the full four-root polynomial target; the generic large-characteristic residual now begins at five active roots.'
    Write-Host 'MILESTONE: the remaining prime Weil input is restricted to the exact cleared Burgess polynomial. Low active-root counts and p<=4*D^2 are discharged internally; the four-root hypergeometric estimate is required only for p>64; and the five-root large-characteristic residual now mentions primeLinearOrderPolynomial rather than arbitrary split polynomials. These source-specific inputs still imply the full cube-free composite endpoint.'
    Write-Host 'MILESTONE: the canonical four-root analytic input is reduced to powers of the single ambient Burgess character, with all three finite exponents normalized below orderOf(chi). Exact pow_mod_orderOf identities transport the finite exponent-range estimate to arbitrary root multiplicities before the source-specific composite bridge is applied.'
    Write-Host 'MILESTONE: scaling the canonical four-root sum puts its finite marked points in Legendre form 0,1,t. The exact reindexing extracts a character-valued constant of norm at most one and reduces the production analytic input to one geometric parameter t!=0,1, one ambient character, and three exponents below orderOf(chi).'
    Write-Host 'MILESTONE: the exact dyadic-prime normalization for Lemma 5.1 is compiled. The half-open band cardinality equals piPrime(2Z)-piPrime(Z); the pinned PNT is transferred from inclusive to strict prime counting; subtraction at the doubled scale proves cardinality asymptotic to Z/log Z; and eventually Z/(2 log Z) is a concrete lower bound for the exact BHM denominator.'
    Write-Host 'MILESTONE: the non-Burgess asymptotic absorption and self-improving bootstrap in Lemma 5.1 are compiled. The Selberg diagonal is O(Z/log Z), while the exact 1-1/5000 off-diagonal envelope is o(Z/log Z). Hence the normalized moment constant is independent of the provisional J<=A*Z^(2/125) coefficient. Finite truncation at floor(A*Z^(2/125)) and the exceptional threshold prove both J<<Z^(2/125) and a bounded squared moment conditional only on the source-shaped explicit cubefree Burgess theorem.'
    Write-Host 'MILESTONE: the full source-shaped Lemma 5.1 output is connected to literal fixed-conductor exceptional finsets. Taking q2=1 gives an injective separated heterogeneous family with exact cardinality and squared-sum preservation. For every varying squarefree q<=Z^3.09, explicit Burgess now implies #Exceptional(q,Z)<<Z^0.016, a bounded squared moment, and the general O(lambda^-2) tail statement.'
    Write-Host 'MILESTONE: the Lemma 5.1 consumer bridge now handles whole finite conductor sets at once. Equality of primitive lcm lifts forces equality of levels and characters, so the dependent conductor-character sigma embeds into one automatically separated q1=1 family. Its total cardinality and complete double squared-moment sum are preserved exactly. Applying explicit Burgess once to the maximal finite admissible squarefree conductor universe gives one eventual constant pointwise for every admissible conductor subset.'
    Write-Host 'MILESTONE: the literal Proposition 6.6 exceptional conductor universe, selector range, and insertion are compiled. Tuple lcms and every nontrivial divisor conductor are squarefree and bounded by cutoff^50. The exact rounded comparison cutoff^50<floor(z^(9/10)) puts all 1001 lower-scale selectors in the Burgess range. Nonnegative subset insertion and the completed logarithmic-lcm Mertens coefficient absorb the exceptional conductor sum into the principal majorant; P_j^(-8)*cutoff^50<=1 absorbs the totient error as well. The entire source-facing small-prime fiftieth moment is bounded by a fixed elementary majorant conditional only on analytic Burgess.'
    Write-Host 'MILESTONE: the Proposition 6.5 condition-(i) source-faithful finite large sieve is compiled. Both square-endpoint orientations are transported to H distinct affine forbidden classes on the exact cofactor range m<=2x/p0^2; smoothness proves avoidance, the tensor ratio is preserved, global Corollary 2.9 bounds both survivor families, and their interval covers recombine with explicit factor 16. Tao literal floor-defined degree and eventual PNT specialization are verified. The PNT lower count yields the exact base H/(8k log(2p0)). Floor maximality gives 2x<(2p0)^(2k+4). Exact AM-GM optimization bounds k>=4 fibers by 128x/(p0*z(x)^6). The paper quarter-comparison gap at k=2,3 is repaired by a valid eighth-comparison for every k>=2; adjusted absorption retains 128x/(p0*z(x)^4). On p0^20<=x^3, every nonempty long fiber automatically supplies the square, degree, PNT, and large-budget side conditions eventually. The dyadic H and reciprocal-p0 sums are finite, their two logarithmic losses are absorbed by one z(x), and the actual long moderate-prime failure union is eventually bounded by x/z(x)^3. The complementary k<4 unsieved bound 4096*x^(9/10) remains available.'
    Write-Host 'MILESTONE: Tao preliminary large-p0 disposal is compiled on the exact ceiling-rounded H<x^(7/50) range. The natural inequalities p0^20>x^3 and H^50<x^7 are bridged to finite cutoffs, the unsieved cofactor cover gives 8Hx/p0^2 per fixed fiber, the dyadic-length and reciprocal-square prime tails are summed, and the actual normalized failure union is eventually at most x^(199/200).'
    Write-Host 'MILESTONE: Tao smooth-number disposals are compiled on actual normalized interval unions. Distinguished p0<=y embeds the small-p0 union into the y-smooth naturals up to 2x; floor(z(x)^beta) preserves the critical exponent, giving 2x/z(x)^(1/beta-epsilon) and the explicit 2x/z(x)^(12/5) specialization. For later prime bands, every fixed (p0,H) fiber is covered by two smooth-cofactor endpoint orientations, giving #fiber<=2H*Psi(floor(2x/p0^2),p0). The actual short union is assembled over all dyadic lengths and a 60-cell exponent grid; log z(2x)/log z(x)->1 transfers the literal source branch z(x)^(5/4)<p0<=ceil(z(x)^3) into the grid, and the fixed exponent margin plus absorbed logarithmic losses yield #union<=x/z(x)^(2+1/800).'
    Write-Host 'MILESTONE: Tao preliminary large-H disposal is compiled on the exact H>=x^(7/50) range. A spare fixed prime-gap exponent 41/300 lies above 2/15 and below 7/50; a finite greedy selection controls all dyadic lengths simultaneously, its disjoint real start segments lie in the literal Proposition 2.3(iii) prime-free endpoint set at scale 2x, and the actual normalized failure union has an existential fixed power saving.'
    Write-Host 'MILESTONE: the matching lower half of Proposition 2.1(ii) is compiled. The exact depth k=Nat.log y X satisfies y^k<=X and differs from log X/log y by less than one; its normalized and logarithmic limits, the frozen-PNT limit log(pi(y))/log_2(x)->A, eventual 2k<=pi(y), the injective prime-subset lattice, and the integral binomial entropy bound yield x^(1-1/A-epsilon)<=Psi(X,y) for every fixed A>1 and epsilon>0.'
    Write-Host 'MILESTONE: the sharp critical lower half of Proposition 2.1(i) is compiled unconditionally. The exact CEP source packet and endpoint-Hildebrand cofactor bridge remain audited. A coarse specialization replaces shrinking bands by disjoint fixed dyadic PNT blocks, proves endpoint reciprocal mass at least 1/(16 log(2) log(u)), chooses multiplicity floor(u-2u/log(u)), bounds the cofactor depth by 10u/log(u), and bounds the complete secondary loss by 60u log(log(u)). This constructs the sharp u*log(u)+o(log z) saddle and yields X/z^(1/alpha+epsilon)<=Psi(X,y). Together with the critical upper theorem and both polylogarithmic bounds, all four quantified halves of Proposition 2.1 are proved. Lemma 1.6(i) is also complete: a fixed prime block z<p<3z gives the lower half, while a rounded sqrt(z) range, finite exponent grid through z^2, alpha+1/alpha>=2, and the reciprocal-square tail give the upper half. For part (ii), literal floor(cX) rounding, logarithmic invariance, critical-regime preservation, the exact Granville-(3.24) quotient-limit target, its IsTheta reduction, and the automatic monotone halves are compiled. The genuine finite saddle is now constructed uniquely from phiOne=log X; phiTwo is positive, phiOne''s derivative is -phiTwo, and the exact two-cutoff secant identity is proved. Explicit Abel-Chebyshev and prime-counting comparisons show that this exact saddle tends to 1 in every critical regime. Its curvature is at least log(2)log(X) and diverges; an exact sensitivity estimate shows fixed dilations move the saddle by o(1/log y). The logarithmic Euler-product phase and Gaussian main term are literal, the phase derivatives are log(X)-phiOne and phiTwo, exponentiation recovers the source Euler product, Rankin is evaluated at the saddle, and the saddle is the unique positive global phase minimum. Uniform prime-local curvature control proves the phiTwo quotient tends to 1 and the complete Gaussian main-term quotient tends to c. The uniform Granville asymptotic, and hence the reverse analytic comparison, remains.'
    Write-Host 'MILESTONE: the smooth saddle is now an explicit local-limit problem. The positive y-smooth Dirichlet weights are normalized to total mass one; their log-partition derivatives are exactly -phiOne and phiTwo; and Psi(X,y) equals exp(phase) times a cutoff factor in [0,1]. At the exact saddle, Psi/mainTerm equals that cutoff factor times the Gaussian scale. The critical saddle asymptotic is proved equivalent to convergence of this explicit quantity to one. The Gaussian local-limit estimate itself remains open.'
    Write-Host 'MILESTONE: the tilted smooth-number weights are now realized as a literal probability measure on logarithmic size. Its characteristic function equals an absolutely convergent Fourier series, is normalized at zero, and has norm at most one. At the exact saddle the log-partition derivatives give center log(X) and positive variance phiTwo; the centered variance-normalized characteristic function is defined and expanded as the exact Fourier series of (log(n)-log(X))/sqrt(phiTwo). Gaussian convergence of this explicit series remains open.'
    Write-Host 'MILESTONE: the tilted characteristic function now has its exact finite-prime Euler product. The complex smooth Dirichlet series is absolutely summable and factors through prime-power geometric series; normalization gives the literal source-prime factors (1-p^(-sigma))/(1-p^(-sigma)exp(i*t*log p)). Each factor has norm at most one, and its squared norm is exactly (1-a)^2/((1-a)^2+2a(1-cos(t log p))). The full centered saddle characteristic therefore has an exact finite contraction product. Uniform frequency estimates and local-limit inversion remain open.'
    Write-Host 'MILESTONE: the central-frequency Gaussian envelope is compiled. On |theta|<=pi, 1-cos(theta)>=2 theta^2/pi^2 gives an explicit rational contraction; on the smaller local window this is at most a Gaussian exponential. The exponent coefficient is exactly each phiTwo summand, so multiplication yields |characteristic(t)|^2<=exp(-2 t^2 phiTwo/pi^2). After exact variance normalization, one source-scale range condition implies the universal bounds |characteristic(t)|^2<=exp(-2t^2/pi^2) and |characteristic(t)|<=exp(-t^2/pi^2). Extending the admissible normalized frequency range and local-limit inversion remain open.'
    Write-Host 'MILESTONE: the finite central frequency window is now explicit. Its positive radius is pi/2*(1-2^(-sigma))*standardDeviation/log(y), membership is equivalent to the source-scale phase condition, and the squared and unsquared universal Gaussian envelopes hold throughout the whole symmetric interval. If log(y)/standardDeviation tends to zero in the critical regime, this radius tends to infinity, so every fixed normalized frequency eventually satisfies the envelope. Proving that curvature-scale limit and carrying out local-limit inversion remain open.'
    Write-Host 'MILESTONE: the critical central frequency window now expands unconditionally. An eight-log Rankin comparison point lies below the exact saddle; antitonicity of phiTwo and the exact secant identity give phiTwo/log(y)^2>=u/(16log(u)) eventually. Hence normalized curvature tends to infinity, log(y)/standardDeviation tends to zero, the explicit central radius tends to infinity, and every fixed normalized frequency eventually obeys the universal Gaussian envelope. Complementary-frequency decay and local-limit inversion remain open.'
    Write-Host 'MILESTONE: the fixed-frequency Gaussian triangular-array transfer is compiled. The normalized saddle characteristic factors exactly into centered prime-local factors whose nonnegative variance shares sum to one. A contraction-product perturbation bound reduces convergence to the summed local quadratic Taylor error; the largest share is at most 20*log(y)^2/phiTwo and therefore tends to zero by the critical curvature theorem. Only the explicit prime-local Taylor remainder remains before pointwise Gaussian characteristic convergence; complementary-frequency decay and inversion remain open.'
    Write-Host 'MILESTONE: the prime-local Taylor boundary and fixed-frequency Gaussian convergence are compiled. Exact centered geometric moments, a uniform third absolute moment bound, and a global cubic exp(ix) remainder give total local error at most 16000*|t|^3*log(y)/standardDeviation, which tends to zero by the critical curvature theorem. The exact normalized saddle characteristic therefore converges to exp(-t^2/2) at every fixed frequency. Complementary-frequency decay and Fourier inversion remain open.'
    Write-Host 'MILESTONE: the remaining saddle cutoff is exactly a one-sided Laplace moment of the centered normalized logarithmic law. Its rate is sigma*sqrt(phiTwo), the Gaussian prefactor is sqrt(2*pi) times this rate, and the rate diverges in every critical regime. The critical saddle asymptotic is equivalent to convergence of this explicit normalized Laplace target; shrinking-scale complementary-frequency control and inversion remain open.'
    Write-Host 'MILESTONE: the central saddle integral is compiled. The exact normalized Laplace kernel lambda/(lambda-i*t) has norm at most one and tends pointwise to one; on the explicit expanding central interval, the kernel-weighted normalized characteristic is dominated by exp(-t^2/pi^2) and converges to exp(-t^2/2). Dominated convergence evaluates the central integral as sqrt(2*pi), so its normalized contribution tends to one. The truncated smooth-number Perron identity and complementary-contour error remain open.'
    Write-Host 'MILESTONE: the normalized central Perron line is source aligned. The twisted smooth Dirichlet series at -t, exp(i*t*log X), and sigma/(sigma+i*t) equal the centered characteristic times lambda/(lambda-i*u) at u=-t*sqrt(phiTwo). The central height rescales exactly to the explicit Gaussian radius, and the full interval substitution identifies the normalized vertical-line contribution with the compiled central Laplace contribution. The sharp cutoff error and complementary line remain open.'
    Write-Host 'MILESTONE: the smooth sharp-Perron cutoff interface is compiled. Absolute convergence passes the smooth Dirichlet series through every finite vertical line and identifies it with the sum of frozen coefficient-free sharp-Perron kernels. The inclusive smooth cutoff sum is exactly psiNat, so the finite-height error is a summable termwise kernel-minus-cutoff series. Frozen logarithmic estimates cover both strict sides of X and the endpoint error is uniformly at most 3/2. Quantitative saddle-scale aggregation and the complementary line remain open.'
    Write-Host 'MILESTONE: symmetric large-height Perron inversion is compiled for the complete smooth series. Individual frozen kernels tend to 1 below X, 1/2 at X, and 0 above X. A summable height-independent envelope justifies Tannery interchange, yielding exactly psiNat minus the explicit possible endpoint half-mass, whose norm is at most 1/2. The finite saddle-height noncentral-line estimate remains open.'
    Write-Host 'MILESTONE: the complementary smooth saddle Perron line is compiled with exact normalization. The complete finite line equals the full frozen-kernel sum divided by the saddle main term; subtracting the central Gaussian contribution is literally the two tail integrals. Its infinite-height limit is the half-endpoint-corrected saddle ratio minus the central term, and critical corrected-ratio convergence is equivalent to vanishing of this named complement. The normalized endpoint is at most 1/(2*mainTerm); main-term divergence and analytic tail decay remain open.'
    Write-Host 'MILESTONE: critical saddle main-term growth is compiled. The curvature satisfies phiTwo<=7*log(y)*phiOne on sigma>=1/2, giving the explicit lower bound sqrt(X)/(sqrt(14*pi)*log X) for the saddle main term. It therefore diverges in every critical regime, the normalized endpoint correction tends to zero, and the original critical saddle asymptotic is exactly equivalent to decay of the named infinite complementary Perron line. Complementary-frequency decay is the sole remaining smooth-saddle input.'
    Write-Host 'MILESTONE: wide-frequency smooth-saddle decay is compiled. Prime-local contraction holds throughout |t log p|<=pi and yields |characteristic(t)|<=exp(-t^2/(48*pi^2)) up to normalized radius pi*standardDeviation/log(y). The annulus outside the expanding central window is Gaussian dominated and its full integral tends to zero in every critical regime. Only Perron frequencies beyond physical height pi/log(y) remain in the complementary line.'
    Write-Host 'MILESTONE: the wide-frequency decay is now matched exactly to the physical Perron line. The wide normalized radius rescales to height pi/log(y), the two signed annular interval substitutions are explicit, and their normalized physical Perron contribution tends to zero in every critical regime. The named complementary line is reduced to its two outer tails beyond this height.'
    Write-Host 'MILESTONE: the two outer Perron tails beyond pi/log(y) are now named at finite and infinite height. The complementary line decomposes exactly into the vanishing principal-phase annulus plus the outer line, the finite outer line tends to its named infinite limit, and the complete critical smooth saddle asymptotic is equivalent to decay of that outer object alone.'
    Write-Host 'MILESTONE: global outer-frequency Euler-product decay is compiled. A nonnegative weighted cosine loss sum over source primes controls every normalized Euler factor, yielding |characteristic(t)| and the literal physical Perron integrand at most exp(-cosineLoss/96) with no phase-range restriction. Outer-tail closure is reduced to a quantitative lower bound for this explicit loss.'
    Write-Host 'MILESTONE: the first outer-frequency shell is quantitatively controlled. On pi/log(y)<=t<=4*pi/(3*log(y)), every prime in the top dyadic block has nonpositive cosine; the compiled Chebyshev--PNT block estimate then gives cosineLoss>=y^(-sigma)*y/(16*log(y)). Later shells and their integrated outer-tail estimate remain.'
    Write-Host 'MILESTONE: an adaptive outer-frequency shell is compiled. The scale N(t)=ceil(exp(pi/t)) lies below y at the outer boundary and its dyadic block remains in the negative-cosine phase window on a controlled small-frequency range; a large Chebyshev--PNT threshold gives cosineLoss>=N(t)^(-sigma)*N(t)/(16*log(N(t))). Larger frequencies and the integrated outer tail remain.'
    Write-Host 'MILESTONE: accumulated first-shell decay is compiled. Every retained CEP dyadic prime block stays in the negative-cosine window, reciprocal mass is of order 1/log(u), and exact saddle/cutoff estimates give a named cosine loss of order at least u/log(u). This loss diverges and uniformly suppresses the physical Perron integrand on the first shell; its normalized integral and later shells remain.'
    Write-Host 'MILESTONE: the complete first outer Perron shell is integrated. Its exact symmetric normalized contribution covers pi/log(y)<=|t|<=4*pi/(3*log(y)); interval length, the accumulated loss envelope, and standardDeviation/log(y)<=sqrt(7u) reduce it to sqrt(u)*exp(-c*u/log(u)), which tends to zero in every critical regime. Later outer-frequency shells and the infinite outer line remain.'
    Write-Host 'MILESTONE: accumulated first-shell decay is extended through physical height 3*pi/(2*log(y)). The retained CEP alphabet stays in the nonpositive-cosine window on this larger range; a reusable symmetric-shell norm bound integrates the adjacent band from 4*pi/(3*log(y)), and its normalized contribution tends to zero. Frequencies beyond the new endpoint remain.'
    Write-Host 'MILESTONE: the first resonant boundary is crossed by a square-root-scale accumulated alphabet. Exact floor-square-root logarithmic bounds and the CEP cutoff put every retained prime between one third and one half of log(y), hence in the nonpositive-cosine phase window for 3*pi/(2*log(y))<=t<=3*pi/log(y). The complete second-shell cosine-loss lower bound is compiled; its divergent-scale conversion and integral remain.'
    Write-Host 'MILESTONE: the complete second outer Perron shell is integrated. Its square-root-alphabet loss is at least a positive constant times u^(2/5)/log(u), this exponential decay absorbs the sqrt(u) saddle normalization, and the exact symmetric contribution for 3*pi/(2*log(y))<=|t|<=3*pi/log(y) tends to zero. Later frequency shells and the infinite outer line remain.'
    Write-Host 'MILESTONE: the next resonant boundary is crossed by an iterated-square-root accumulated alphabet. Exact floor-root bounds put its logarithmic support between one sixth and one quarter of log(y), hence in the nonpositive-cosine phase window for 3*pi/log(y)<=t<=6*pi/log(y). The complete third-shell cosine-loss lower bound is compiled; its divergent-scale conversion and integral remain.'
    Write-Host 'MILESTONE: the complete third outer Perron shell is integrated. Its fourth-root-alphabet loss is at least a positive constant times u^(1/5)/log(u), this exponential decay absorbs the sqrt(u) saddle normalization, and the exact symmetric contribution for 3*pi/log(y)<=|t|<=6*pi/log(y) tends to zero. Later frequency shells and the infinite outer line remain.'
    Write-Host 'MILESTONE: the next resonant boundary is crossed by an eighth-root accumulated alphabet. Exact iterated-floor bounds put its retained logarithmic support between one twelfth and one eighth of log(y), hence in the nonpositive-cosine phase window for 6*pi/log(y)<=t<=12*pi/log(y). The complete fourth-shell cosine-loss lower bound is compiled; its divergent-scale conversion and integral remain.'
    Write-Host 'MILESTONE: the complete fourth outer Perron shell is integrated. Its eighth-root-alphabet loss is at least a positive constant times u^(1/9)/log(u), this exponential absorbs the saddle normalization, and the exact symmetric contribution through 12*pi/log(y) tends to zero. Later shells and the infinite outer line remain.'
    Write-Host 'MILESTONE: the repeated outer-shell construction now has indexed infrastructure. Arbitrary iterated natural square-root alphabets have closed-form lower and upper logarithmic envelopes, recover the certified concrete scales, and carry physical shell endpoints that double exactly. Uniform indexed phase loss and infinite aggregation remain.'
    Write-Host 'MILESTONE: uniform indexed phase loss is compiled. At every k>=2, one four-fifths lower bound for the ideal iterated-root logarithmic scale gives the retained CEP support, exact nonpositive-cosine phase window between adjacent indexed heights, and the full accumulated cosine-loss bound. Growing-range verification and shell summation remain.'
    Write-Host 'MILESTONE: the indexed scale range is explicit. Iterated roots are antitone, terminal noncollapse controls every preceding scale, and 10*(2^k-1)*log(2)<=log(y) implies the four-fifths logarithmic retention required by the uniform phase theorem. A growing terminal-index choice and aggregate tail estimate remain.'

    Write-Host 'MILESTONE: the Proposition 6.6 typical-tuple count is assembled over every ordered 1001-coordinate moving dyadic scale. Tao enlarged bands map globally into B1 at one fixed dilation; canonical recovery of the largest 1000 prime factors gives the absolute global fiber bound 1000^1000. PNT comparison costs 8^1001, the explicit unweighted and length-weighted assembly factors tend to zero, and both global counts are little-o of the dilated one-term count conditional on explicit Burgess.'
Write-Host 'MILESTONE: every actual typical interval in both endpoint orientations has a canonical injective code into a global weighted family. The forward tuple start is exactly N+1, the reflected tuple start is exactly N+H, and both codes recover length H. The symmetric v-l small-prime moment, reflected source mean/variance, Markov-Chebyshev normalization, uniform support count, and backward all-scale weighted assembly are compiled. The quantitative typical estimate and Proposition 6.5 slow diagonal each retain a 1/log(x)^(1-o(1)) saving relative to the appropriate one-term count. Their exact partition, Lemma 1.6(ii) fixed-dilation removal, and the factor-30 maximal transfer give the conditional local dyadic-window bound. An exact finite power-of-two cover bounds the global nontrivial bad count by the sum of those windows. A slowly widening central packet carries asymptotically all B1 mass; the sharp critical smooth-number dilation limit proves B1(x/2)/B1(x)->1/2 and hence the adjacent ratio B1(2^r)/B1(2^(r+1))->1/2. The half-ratio iterates through powers of two, and exact floor bracketing proves the complete Lemma 1.6(ii) contract for every fixed positive dilation. Logarithmic weights contract geometrically, finite early scales are absorbed, the top endpoint lies in [x,2x], and both clauses of the exact Theorem 1.7 contract follow conditionally. The all-start large-length Sylvester--Schur tail and the explicit H^H+1 fixed-length thresholds give one common start cutoff; admissible starts eventually cross it, removing unrestricted Sylvester--Schur from this dependency chain. The sharp critical smooth-number saddle asymptotic and analytic Burgess are the two remaining Theorem 1.7 inputs; no unconditional Theorem 1.7 release is claimed.'

    Write-Host 'FINAL RESULT: PASS - Tao Proposition 2.3(i),(iii), all four quantified Proposition 2.1 bounds, complete Lemma 1.6(i), exact B1/VB1 sums, exact smooth-number Euler product, finite Rankin/Abel-Chebyshev bound, exact finite saddle existence/uniqueness/derivative/secant theory, critical-regime limit to 1, divergent curvature, fixed-dilation o(1/log y) displacement, exact saddle phase/main-term/global-minimum theory, and complete Gaussian saddle-main-term dilation ratio, both quantified upper and lower halves of the polylogarithmic Proposition 2.1(ii), the VB1 zeta-ratio asymptotic, complete Lemmas 2.10, 3.2, and 4.3, complete signed uniform Corollary 2.11, and audited Theorem 2.5 complex source contract/j1-absorption/phase-character-variation/qualitative-PNT dyadic and bounded-frequency consequences/low-frequency Abel-PNT reduction/finite Fourier assembly, uniform-approximation transfer, finite l1 truncation tails, summable cubic Z2 envelope, vanishing square-box tails, torus descent, conditional uniform reconstruction of W, complete smooth-periodic radial C3 Fourier decay/source-oriented Vaughan coefficient bounds and supports/product-restricted convolution/canonical polynomial-log short-family coverage, exact weighted Type-I/II decomposition, literal real-log relative-width support, exact ceiling-divided correlation-interval rewrite, and unconditional sharp-lag finite van-der-Corput recursion with arbitrary-depth majorant, exact source four-step specialization, positive-ray exact-interval finite-difference FTC bridges with arbitrary lag-product upper/regular-lower estimates, IVT sign separation, terminal first/second derivative windows, a critical-regular nonlinear Kusmin-Landau terminal bound, exact rH/H^r admissible-lag control, uniform arbitrary-depth plus literal four-round regular-interval closure, exact lag-sensitive Weyl-tree propagation with an inverse-product/truncation leaf profile, harmonic leaf summation, all-depth scalar closure with generalized harmonic factors bounded by H, a source four-round sixteenth-root estimate, and a coarse scale recurrence with exact (QH)^15/scale sixteenth power, four explicit diagonal terms with exact sixteenth powers and powered denominator bounds, an exact source-facing five-term real-1/16-power majorant, a canonical floor-rounded differencing range with automatic upper-smallness discharge, and exact expanded-critical-start counting plus global long/short regular-component assembly, and terminal affine geometric-sum plus nearest-integer-distance estimate/prime-power/Abel/Type-I/complete-finite-product-restricted-Type-II/necessary all-support endpoint plus endpoint-free pure off-diagonal distance-kernel propagation through exact Vaughan double blocks and source-facing block lengths/high-frequency-log-absorption/normalized-parameter-bounds/critical-deletion groundwork, together with exact equation-(18)/Lemma-12/scalar-growth/native-Wooley-VMVT count bridges/critical box-power ledger/critical assembly/sharp quarter-window R^2/193 saving/exact root/source-decay conversion/exact p-adic concentration-data coefficient bridge, a uniform absolute-coefficient positive Ford benchmark at moment 4R^2 for R>=10000, finite native critical-coefficient absorption reducing the exact rooted residual to R>=1000, the exact factorial-fiber reduction with unconditional long-interval and length-two square obstructions, full-to-core ES equivalence, two-element fiber consequence, and conditional finite Theorem 1.10 upper transfer #triples<=2g#F3, plus the complete source-facing Proposition 6.5 slow-cutoff diagonal with both exact cutoff log-ratios tending to one and a 1/log(x)^(1-o(1)) saving normalized by actual B1, the conditional all-scale Proposition 6.6 typical-tuple assembly with the matching explicit saving, exact typical/non-typical recombination and factor-30 maximal transfer, the eventual admissible-scale large-prime theorem, the conditional local dyadic-window estimate, exact finite global dyadic cover, slow central-packet concentration, the half-ratio and adjacent B1 ratio plus the full Lemma 1.6(ii) fixed-dilation comparison derived from the sharp critical smooth-number dilation limit, adjacent-ratio geometric summation, and exact conditional Theorem 1.7 contract without unrestricted Sylvester--Schur; the sharp critical smooth-number saddle asymptotic and analytic Burgess remain its two inputs, and no unconditional main-theorem release is claimed.'
    Write-Host 'RELEASE STATUS: Tao Theorem 1.8 is now unconditional; the combined Theorems 1.7--1.10 release is not yet claimed.'
    exit 0
}
catch {
    Write-Error $_
    exit 1
}
