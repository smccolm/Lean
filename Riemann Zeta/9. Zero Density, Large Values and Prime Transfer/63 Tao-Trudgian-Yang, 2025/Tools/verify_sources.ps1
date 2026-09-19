[CmdletBinding()]
param()

$ErrorActionPreference = 'Stop'
$projectRoot = Split-Path -Parent $PSScriptRoot
$sourceRoot = Join-Path $projectRoot 'Sources'
$ledgerPath = Join-Path $sourceRoot 'SHA256SUMS.txt'

if (-not (Test-Path -LiteralPath $ledgerPath -PathType Leaf)) {
    throw "Missing source hash ledger: $ledgerPath"
}

$failures = [System.Collections.Generic.List[string]]::new()
$checked = 0

foreach ($line in Get-Content -LiteralPath $ledgerPath) {
    if ([string]::IsNullOrWhiteSpace($line) -or $line.StartsWith('#')) {
        continue
    }

    if ($line -notmatch '^([0-9a-fA-F]{64})  (.+)$') {
        $failures.Add("Malformed ledger line: $line")
        continue
    }

    $expected = $Matches[1].ToLowerInvariant()
    $relative = $Matches[2]
    $nativeRelative = $relative.Replace('/', [IO.Path]::DirectorySeparatorChar)
    $path = Join-Path $sourceRoot $nativeRelative

    if (-not (Test-Path -LiteralPath $path -PathType Leaf)) {
        $failures.Add("Missing: $relative")
        continue
    }

    $actual = (Get-FileHash -LiteralPath $path -Algorithm SHA256).Hash.ToLowerInvariant()
    if ($actual -ne $expected) {
        $failures.Add("Hash mismatch: $relative`n  expected $expected`n  actual   $actual")
        continue
    }

    $checked++
    Write-Host "PASS $relative"
}

$listed = Get-Content -LiteralPath $ledgerPath |
    Where-Object { $_ -match '^[0-9a-fA-F]{64}  (.+)$' } |
    ForEach-Object { $Matches[1].Replace('\', '/') }

$actualFiles = Get-ChildItem -LiteralPath $sourceRoot -Recurse -File |
    Where-Object { $_.FullName -ne $ledgerPath } |
    ForEach-Object {
        $_.FullName.Substring($sourceRoot.Length + 1).Replace('\', '/')
    }

foreach ($unlisted in Compare-Object -ReferenceObject $listed -DifferenceObject $actualFiles |
    Where-Object SideIndicator -eq '=>' |
    ForEach-Object InputObject) {
    $failures.Add("Unlisted source file: $unlisted")
}

if ($failures.Count -ne 0) {
    foreach ($failure in $failures) {
        Write-Error $failure
    }
    throw "Source verification failed with $($failures.Count) issue(s)."
}

Write-Host "SOURCE VERIFICATION PASS: $checked pinned files"
