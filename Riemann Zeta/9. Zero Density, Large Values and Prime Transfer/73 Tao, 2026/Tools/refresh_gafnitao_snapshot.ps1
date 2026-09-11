$ErrorActionPreference = 'Stop'

$nodeRoot = Split-Path -Parent $PSScriptRoot
$chapterRoot = Split-Path -Parent $nodeRoot
$sourceNode = Join-Path $chapterRoot '74 Gafni-Tao, 2026'
$sourceExtension = Join-Path $sourceNode 'Extension'
$sourcePnt = Join-Path $sourceNode 'Dependencies\PrimeNumberTheoremAndClean'
$destination = Join-Path $nodeRoot 'Dependencies\GafniTaoFrozen'

if (-not (Test-Path -LiteralPath $sourceExtension -PathType Container)) {
    throw "Missing Gafni-Tao source node: $sourceExtension"
}
if (-not (Test-Path -LiteralPath $sourcePnt -PathType Container)) {
    throw "Missing PNT+ source package: $sourcePnt"
}
New-Item -ItemType Directory -Path $destination -Force | Out-Null

function Resolve-LocalModule {
    param([Parameter(Mandatory = $true)][string]$Module)

    $modulePath = $Module.Replace('.', '\') + '.lean'
    if ($Module -eq 'GafniTao' -or $Module.StartsWith('GafniTao.')) {
        $source = Join-Path $sourceExtension $modulePath
        $relative = $modulePath
    }
    elseif ($Module -eq 'RiemannZeta' -or $Module.StartsWith('RiemannZeta.')) {
        $source = Join-Path (Join-Path $sourceExtension 'FrozenFoundation') $modulePath
        $relative = Join-Path 'FrozenFoundation' $modulePath
    }
    elseif ($Module -eq 'PrimeNumberTheoremAnd' -or
            $Module.StartsWith('PrimeNumberTheoremAnd.')) {
        $source = Join-Path $sourcePnt $modulePath
        $relative = Join-Path 'PrimeNumberTheoremAndClean' $modulePath
    }
    else {
        return $null
    }

    if (-not (Test-Path -LiteralPath $source -PathType Leaf)) {
        throw "Local import does not resolve: $Module ($source)"
    }
    return [pscustomobject]@{ Module = $Module; Source = $source; Relative = $relative }
}

$queue = [System.Collections.Generic.Queue[string]]::new()
@(
    'GafniTao.Theorem11',
    'GafniTao.WooleySourceCriticalBase',
    'GafniTao.WooleySourceToPadic',
    'GafniTao.WooleyPadicToCritical'
) | ForEach-Object { $queue.Enqueue($_) }
$seen = [System.Collections.Generic.HashSet[string]]::new([System.StringComparer]::Ordinal)
$closure = [System.Collections.Generic.List[object]]::new()

while ($queue.Count -gt 0) {
    $module = $queue.Dequeue()
    if (-not $seen.Add($module)) { continue }
    $resolved = Resolve-LocalModule -Module $module
    if ($null -eq $resolved) { continue }
    $closure.Add($resolved)

    foreach ($line in Get-Content -LiteralPath $resolved.Source) {
        if ($line -notmatch '^\s*(?:public\s+)?import\s+(.+?)\s*(?:--.*)?$') { continue }
        foreach ($imported in ($Matches[1] -split '\s+')) {
            if (-not $imported) { continue }
            if ($imported -eq 'GafniTao' -or $imported.StartsWith('GafniTao.') -or
                $imported -eq 'RiemannZeta' -or $imported.StartsWith('RiemannZeta.') -or
                $imported -eq 'PrimeNumberTheoremAnd' -or
                $imported.StartsWith('PrimeNumberTheoremAnd.')) {
                $queue.Enqueue($imported)
            }
        }
    }
}

foreach ($entry in $closure) {
    $target = Join-Path $destination $entry.Relative
    New-Item -ItemType Directory -Path (Split-Path -Parent $target) -Force | Out-Null
    Copy-Item -LiteralPath $entry.Source -Destination $target -Force
}

$metadata = @(
    @{ Source = (Join-Path $sourceExtension 'FROZEN_FOUNDATION.md'); Relative = 'UPSTREAM_FROZEN_FOUNDATION.md' },
    @{ Source = (Join-Path $sourceExtension 'FrozenFoundation\SHA256SUMS.txt'); Relative = 'UPSTREAM_FOUNDATION_SHA256SUMS.txt' },
    @{ Source = (Join-Path $sourceExtension 'lean-toolchain'); Relative = 'lean-toolchain' },
    @{ Source = (Join-Path $sourcePnt 'README.md'); Relative = 'PrimeNumberTheoremAndClean\README.md' },
    @{ Source = (Join-Path $sourcePnt 'SOURCE_SHA256SUMS.txt'); Relative = 'PrimeNumberTheoremAndClean\SOURCE_SHA256SUMS.txt' },
    @{ Source = (Join-Path $sourcePnt 'lakefile.toml'); Relative = 'PrimeNumberTheoremAndClean\UPSTREAM_lakefile.toml' },
    @{ Source = (Join-Path $sourcePnt 'lake-manifest.json'); Relative = 'PrimeNumberTheoremAndClean\UPSTREAM_lake-manifest.json' },
    @{ Source = (Join-Path $sourcePnt 'lean-toolchain'); Relative = 'PrimeNumberTheoremAndClean\lean-toolchain' }
)
foreach ($entry in $metadata) {
    if (-not (Test-Path -LiteralPath $entry.Source -PathType Leaf)) {
        throw "Missing upstream metadata file: $($entry.Source)"
    }
    $target = Join-Path $destination $entry.Relative
    New-Item -ItemType Directory -Path (Split-Path -Parent $target) -Force | Out-Null
    Copy-Item -LiteralPath $entry.Source -Destination $target -Force
}

$manifestPath = Join-Path $destination 'SOURCE_SHA256SUMS.txt'
$manifestLines = foreach ($entry in $closure | Sort-Object Relative) {
    $target = Join-Path $destination $entry.Relative
    $relative = $entry.Relative.Replace('\', '/')
    '{0}  {1}' -f (Get-FileHash -LiteralPath $target -Algorithm SHA256).Hash, $relative
}
Set-Content -LiteralPath $manifestPath -Value $manifestLines -Encoding ascii

$counts = $closure | Group-Object {
    if ($_.Module -eq 'GafniTao' -or $_.Module.StartsWith('GafniTao.')) { 'GafniTao' }
    elseif ($_.Module -eq 'RiemannZeta' -or $_.Module.StartsWith('RiemannZeta.')) { 'RiemannZeta' }
    else { 'PrimeNumberTheoremAnd' }
} | Sort-Object Name

foreach ($count in $counts) {
    Write-Host ("{0}: {1} modules" -f $count.Name, $count.Count)
}
Write-Host ("Frozen closure: {0} modules" -f $closure.Count)
Write-Host "Manifest: $manifestPath"
