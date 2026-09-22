[CmdletBinding()]
param()

$ErrorActionPreference = 'Stop'
$projectRoot = Split-Path -Parent $PSScriptRoot
$sourceRoot = (Resolve-Path -LiteralPath (
    Join-Path $projectRoot 'Dependencies\GafniTaoNative')).Path
$ledgerPath = Join-Path $sourceRoot 'SOURCE_SHA256SUMS.txt'
$sourcePrefix = $sourceRoot.TrimEnd('\') + '\'
$listed = [Collections.Generic.HashSet[string]]::new(
    [StringComparer]::OrdinalIgnoreCase)
$ledgerLines = @(Get-Content -LiteralPath $ledgerPath -Encoding UTF8 |
    Where-Object { -not [string]::IsNullOrWhiteSpace($_) })
if ($ledgerLines.Count -ne 469) {
    throw "Expected 469 pinned Gafni-Tao source/configuration files, found $($ledgerLines.Count)."
}
foreach ($line in $ledgerLines) {
    if ($line -notmatch '^([0-9a-fA-F]{64})  (.+)$') {
        throw "Malformed Gafni-Tao source ledger entry: $line"
    }
    $expectedHash = $Matches[1]
    $relativePath = $Matches[2].Replace('/', '\')
    if (-not $listed.Add($relativePath)) {
        throw "Duplicate Gafni-Tao source entry: $relativePath"
    }
    $sourcePath = [IO.Path]::GetFullPath((Join-Path $sourceRoot $relativePath))
    if (-not $sourcePath.StartsWith($sourcePrefix, [StringComparison]::OrdinalIgnoreCase)) {
        throw "Gafni-Tao source path escapes the pinned package: $relativePath"
    }
    if (-not (Test-Path -LiteralPath $sourcePath -PathType Leaf)) {
        throw "Missing Gafni-Tao source: $relativePath"
    }
    if ((Get-FileHash -LiteralPath $sourcePath -Algorithm SHA256).Hash -ne $expectedHash) {
        throw "Gafni-Tao source hash mismatch: $relativePath"
    }
}
$actualFiles = @(Get-ChildItem -LiteralPath $sourceRoot -Recurse -File |
    Where-Object {
        $_.FullName -notmatch '[\\/]\.lake[\\/]' -and
        $_.FullName -ne $ledgerPath
    })
foreach ($file in $actualFiles) {
    $relativePath = $file.FullName.Substring($sourcePrefix.Length)
    if (-not $listed.Contains($relativePath)) {
        throw "Unmanifested Gafni-Tao package file: $relativePath"
    }
}
if ($actualFiles.Count -ne $ledgerLines.Count) {
    throw 'Gafni-Tao source inventory differs from its hash ledger.'
}

$modulePaths = @{}
foreach ($file in $actualFiles | Where-Object { $_.Extension -eq '.lean' }) {
    $relativePath = $file.FullName.Substring($sourcePrefix.Length)
    $moduleName = $relativePath.Substring(0, $relativePath.Length-5).Replace('\', '.')
    if ($modulePaths.ContainsKey($moduleName)) {
        throw "Duplicate pinned module: $moduleName"
    }
    $modulePaths[$moduleName] = $file.FullName
}
if ($modulePaths.Count -ne 463) {
    throw "Expected 463 pinned Lean modules, found $($modulePaths.Count)."
}
$pending = [Collections.Generic.Queue[string]]::new()
$reachable = [Collections.Generic.HashSet[string]]::new([StringComparer]::Ordinal)
$pending.Enqueue('GafniTaoNative')
while ($pending.Count -gt 0) {
    $moduleName = $pending.Dequeue()
    if (-not $reachable.Add($moduleName)) { continue }
    if (-not $modulePaths.ContainsKey($moduleName)) {
        throw "Missing reachable pinned module: $moduleName"
    }
    $sourceText = Get-Content -LiteralPath $modulePaths[$moduleName] -Raw -Encoding UTF8
    foreach ($import in [regex]::Matches($sourceText, '(?m)^(?:public )?import\s+([A-Za-z0-9_.]+)')) {
        $importName = $import.Groups[1].Value
        if ($importName.StartsWith('RiemannZeta.')) {
            throw "Frozen-foundation import remains in $moduleName : $importName"
        }
        if ($importName -in @('PrimeNumberTheoremAnd.Wiener', 'PrimeNumberTheoremAnd.Consequences')) {
            throw "Monolithic PNT import remains in $moduleName : $importName"
        }
        if ($importName.StartsWith('GafniTao.')) { $pending.Enqueue($importName) }
    }
}
foreach ($moduleName in $modulePaths.Keys) {
    if (-not $reachable.Contains($moduleName)) {
        throw "Pinned source excluded from the boundary import closure: $moduleName"
    }
}
Write-Host "PASS: pinned Gafni-Tao source integrity ($($ledgerLines.Count) files, $($reachable.Count) reachable Lean modules)"
