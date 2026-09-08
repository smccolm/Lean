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
        'Extension\lake-manifest.json',
        'Extension\lakefile.toml',
        'Extension\lean-toolchain',
        'Extension\Tao2026.lean',
        'Extension\Tao2026\Anatomy.lean',
        'Extension\Tao2026\Asymptotics.lean',
        'Extension\Tao2026\Audit.lean',
        'Extension\Tao2026\Counting.lean',
        'Extension\Tao2026\Intervals.lean',
        'Sources\PINS.md',
        'Sources\SHA256SUMS.txt',
        'Sources\tao-unusual-anatomy-2603.27990v2.pdf',
        'Sources\tao-unusual-anatomy-2603.27990v2.tar',
        'Tools\README.md',
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
    if ($hashLines.Count -ne 2) {
        throw 'SHA256SUMS.txt must contain exactly the pinned PDF and TeX archive.'
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

    Write-Host 'Checking production-root coverage and forbidden proof shortcuts...'
    $leanFiles = @(
        Get-ChildItem -LiteralPath $extensionRoot -Recurse -File -Filter '*.lean' |
            Where-Object { $_.FullName -notmatch '[\\/]\.lake[\\/]' }
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

    Write-Host 'FINAL RESULT: PASS - initial definitions milestone; no Tao theorem release is claimed.'
    exit 0
}
catch {
    Write-Error $_
    exit 1
}
