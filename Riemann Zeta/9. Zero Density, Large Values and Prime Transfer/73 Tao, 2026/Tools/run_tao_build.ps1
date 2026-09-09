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
        'Dependencies\GafniTaoFrozen\PrimeNumberTheoremAndClean\lakefile.toml',
        'Extension\lake-manifest.json',
        'Extension\lakefile.toml',
        'Extension\lean-toolchain',
        'Extension\Tao2026.lean',
        'Extension\Tao2026\Anatomy.lean',
        'Extension\Tao2026\Asymptotics.lean',
        'Extension\Tao2026\Audit.lean',
        'Extension\Tao2026\CoefficientBounds.lean',
        'Extension\Tao2026\CoefficientProduct.lean',
        'Extension\Tao2026\CoefficientSelection.lean',
        'Extension\Tao2026\ConvolutionRearrangement.lean',
        'Extension\Tao2026\Counting.lean',
        'Extension\Tao2026\CriticalIntervals.lean',
        'Extension\Tao2026\FactorialAsymptotics.lean',
        'Extension\Tao2026\FactorialFibers.lean',
        'Extension\Tao2026\FactorialIntervals.lean',
        'Extension\Tao2026\FactorialOneTerm.lean',
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
        'Extension\Tao2026\ShortIntervalDecomposition.lean',
        'Extension\Tao2026\TypeIReduction.lean',
        'Extension\Tao2026\TypeIIReduction.lean',
        'Extension\Tao2026\TypeIIKernel.lean',
        'Extension\Tao2026\VeryBadIntervals.lean',
        'Extension\Tao2026\VinogradovPhase.lean',
        'Extension\Tao2026\VaughanIdentity.lean',
        'Sources\PINS.md',
        'Sources\SHA256SUMS.txt',
        'Sources\baker-harman-pintz-2001.pdf',
        'Sources\erdos-selfridge-1975.pdf',
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
    if ($hashLines.Count -ne 6) {
        throw 'SHA256SUMS.txt must contain exactly the Tao PDF and TeX archive, Baker-Harman-Pintz PDF, Erdos-Selfridge PDF, and Singmaster PDF and TeX archive.'
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
    if ($frozenHashLines.Count -ne 1226) {
        throw "Frozen source manifest must contain exactly 1226 modules; found $($frozenHashLines.Count)."
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
    if ($actualFrozenFiles.Count -ne 1226) {
        throw "Frozen dependency must contain exactly 1226 Lean modules; found $($actualFrozenFiles.Count)."
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

    Write-Host 'FINAL RESULT: PASS - Tao Proposition 2.3(i),(iii), exact B1/VB1 sums, the VB1 zeta-ratio asymptotic, complete Lemmas 2.10 and 3.2, complete signed uniform Corollary 2.11, and audited Theorem 2.5 complex source contract/j1-absorption/phase-character-variation/qualitative-PNT dyadic and bounded-frequency consequences/low-frequency Abel-PNT reduction/finite Fourier assembly, uniform-approximation transfer, finite l1 truncation tails, summable cubic Z2 envelope, vanishing square-box tails, torus descent, conditional uniform reconstruction of W, complete smooth-periodic radial C3 Fourier decay/Vaughan/product-restricted-convolution/outer-and-double-coefficient-blocks/prime-power/Abel/Type-I/complete-finite-product-restricted-Type-II/necessary all-support endpoint plus endpoint-free pure off-diagonal distance-kernel propagation through exact Vaughan double blocks and source-facing block lengths/high-frequency-log-absorption/normalized-parameter-bounds/critical-deletion groundwork; no main-theorem release is claimed.'
    exit 0
}
catch {
    Write-Error $_
    exit 1
}
