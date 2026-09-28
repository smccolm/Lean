[CmdletBinding()]
param([string] $RuntimeRoot)

$ErrorActionPreference = 'Stop'
$projectRoot = Split-Path -Parent $PSScriptRoot
$workspaceRoot = (Get-Item -LiteralPath $projectRoot).Parent.Parent.Parent.FullName
if (-not $RuntimeRoot) {
    $RuntimeRoot = Join-Path $workspaceRoot '.tmp_epzae_reproduction_20260927'
}
$runtimePath = [IO.Path]::GetFullPath($RuntimeRoot)
$workspacePrefix = [IO.Path]::GetFullPath($workspaceRoot).TrimEnd('\') + '\'
if (-not $runtimePath.StartsWith($workspacePrefix, [StringComparison]::OrdinalIgnoreCase) -or
    $runtimePath.TrimEnd('\') -eq $workspacePrefix.TrimEnd('\')) {
    throw 'The isolated reproduction runtime must be inside the Lean workspace.'
}
$lock = Get-Content -Encoding UTF8 -Raw -LiteralPath (Join-Path $PSScriptRoot 'paper_time_environment.json') |
    ConvertFrom-Json
Add-Type -AssemblyName System.IO.Compression.FileSystem
if (-not (Test-Path -LiteralPath $runtimePath)) {
    New-Item -ItemType Directory -Path $runtimePath | Out-Null
}

function Confirm-Artifact {
    param([string] $Path, [string] $ExpectedHash)
    if ((Get-FileHash -Algorithm SHA256 -LiteralPath $Path).Hash.ToLowerInvariant() -ne $ExpectedHash) {
        throw "Pinned artifact checksum mismatch: $Path"
    }
}

$pythonArchive = Join-Path $runtimePath $lock.python.file
if (-not (Test-Path -LiteralPath $pythonArchive)) {
    Write-Host 'Downloading the pinned isolated Python runtime from python.org.'
    Invoke-WebRequest -UseBasicParsing -Uri $lock.python.url -OutFile $pythonArchive
}
Confirm-Artifact $pythonArchive $lock.python.sha256
$pythonDirectory = Join-Path $runtimePath 'python'
if (-not (Test-Path -LiteralPath $pythonDirectory)) {
    [IO.Compression.ZipFile]::ExtractToDirectory($pythonArchive, $pythonDirectory)
}
$wheelDirectory = Join-Path $runtimePath 'wheels'
if (-not (Test-Path -LiteralPath $wheelDirectory)) {
    New-Item -ItemType Directory -Path $wheelDirectory | Out-Null
}
foreach ($wheel in $lock.wheels) {
    $wheelPath = Join-Path $wheelDirectory $wheel.file
    if (-not (Test-Path -LiteralPath $wheelPath)) {
        $parts = $wheel.file.Split('-')
        $name = $parts[0].Replace('_', '-')
        $version = $parts[1]
        $metadata = Invoke-RestMethod -Uri "https://pypi.org/pypi/$name/$version/json"
        $matches = @($metadata.urls | Where-Object {
            $_.filename -eq $wheel.file -and $_.digests.sha256 -eq $wheel.sha256
        })
        if ($matches.Count -ne 1) { throw "Pinned PyPI wheel not found: $($wheel.file)" }
        $downloadUri = [Uri]$matches[0].url
        if ($downloadUri.Scheme -ne 'https' -or $downloadUri.Host -ne 'files.pythonhosted.org') {
            throw 'Unexpected PyPI artifact host.'
        }
        Write-Host "Downloading pinned $($wheel.file)"
        Invoke-WebRequest -UseBasicParsing -Uri $downloadUri -OutFile $wheelPath
    }
    Confirm-Artifact $wheelPath $wheel.sha256
}
$packages = Join-Path $runtimePath 'site-packages'
if (-not (Test-Path -LiteralPath $packages)) {
    New-Item -ItemType Directory -Path $packages | Out-Null
    foreach ($wheel in $lock.wheels) {
        # The pinned wheels contain their importable modules and native DLLs
        # directly at wheel root. Launcher/header payloads are not executed.
        [IO.Compression.ZipFile]::ExtractToDirectory(
            (Join-Path $wheelDirectory $wheel.file), $packages)
    }
}
Write-Host "Pinned runtime artifacts ready: $runtimePath"
Write-Host 'The replay additionally checks installed module/runtime bytes before execution.'

