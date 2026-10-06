param([string]$SourceRoot = (Join-Path $PSScriptRoot '..\Sources'))

Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'
$sourcePath = (Resolve-Path -LiteralPath $SourceRoot).Path.TrimEnd('\', '/')
$sourcePrefix = $sourcePath + [IO.Path]::DirectorySeparatorChar
$ledger = Join-Path $sourcePath 'SHA256SUMS.txt'
$expected = @{}
foreach ($line in Get-Content -LiteralPath $ledger -Encoding UTF8) {
    if ([string]::IsNullOrWhiteSpace($line) -or $line.StartsWith('#')) { continue }
    if ($line -notmatch '^([0-9a-fA-F]{64})  (.+)$') { throw "Malformed source pin: $line" }
    $hash = $Matches[1]
    $relative = $Matches[2].Replace('\', '/')
    if ([IO.Path]::IsPathRooted($relative) -or $relative.Split('/') -contains '..') {
        throw "Nonlocal source pin: $relative"
    }
    if ($expected.ContainsKey($relative)) { throw "Duplicate source pin: $relative" }
    if ($relative -in @('README.md', 'PINS.md', 'SHA256SUMS.txt')) {
        throw "Metadata cannot be an artifact pin: $relative"
    }
    $path = [IO.Path]::GetFullPath((Join-Path $sourcePath $relative))
    if (-not $path.StartsWith($sourcePrefix, [StringComparison]::OrdinalIgnoreCase)) {
        throw "Source pin escapes source directory: $relative"
    }
    if (-not (Test-Path -LiteralPath $path -PathType Leaf)) { throw "Missing source: $relative" }
    if ((Get-FileHash -LiteralPath $path -Algorithm SHA256).Hash -ne $hash) {
        throw "Source hash mismatch: $relative"
    }
    $expected[$relative] = $hash
}
if ($expected.Count -eq 0) { throw 'Empty source ledger' }
foreach ($file in Get-ChildItem -LiteralPath $sourcePath -Recurse -File -Force) {
    $relative = $file.FullName.Substring($sourcePrefix.Length).Replace('\', '/')
    if ($relative -in @('README.md', 'PINS.md', 'SHA256SUMS.txt')) { continue }
    if (-not $expected.ContainsKey($relative)) { throw "Unpinned source: $relative" }
}
Write-Output "SOURCE PINS PASS: $($expected.Count) artifacts; complete inventory and SHA-256."
