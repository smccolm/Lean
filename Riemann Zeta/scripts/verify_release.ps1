param(
  [ValidateSet("development", "release")]
  [string]$Mode = "development",
  [string]$LogPath = "",
  [string]$ManifestPath = ""
)

$ErrorActionPreference = "Stop"
Set-StrictMode -Version Latest

$VerifierVersion = "gm-foundation-freeze-v1"
$ProjectRoot = (Resolve-Path (Join-Path $PSScriptRoot "..")).Path
$GitRoot = (& git -C $ProjectRoot rev-parse --show-toplevel 2>$null)
if ($LASTEXITCODE -ne 0 -or [string]::IsNullOrWhiteSpace($GitRoot)) {
  throw "Cannot resolve the Git repository root from $ProjectRoot"
}
$GitRoot = (Resolve-Path $GitRoot.Trim()).Path

$Lake = $env:LAKE_EXE
if ([string]::IsNullOrWhiteSpace($Lake)) {
  $LakeCommand = Get-Command lake -ErrorAction SilentlyContinue
  if ($null -ne $LakeCommand) {
    $Lake = $LakeCommand.Source
  } else {
    $Candidate = Join-Path $env:USERPROFILE ".elan\bin\lake.exe"
    if (Test-Path -LiteralPath $Candidate) { $Lake = $Candidate }
  }
}
if ([string]::IsNullOrWhiteSpace($Lake) -or !(Test-Path -LiteralPath $Lake)) {
  throw "lake executable not found; install Elan and the pinned toolchain first"
}

$Timestamp = Get-Date
$Stamp = $Timestamp.ToString("yyyyMMdd_HHmmss")
$LogsDirectory = Join-Path $ProjectRoot "logs"
New-Item -ItemType Directory -Force -Path $LogsDirectory | Out-Null
if ([string]::IsNullOrWhiteSpace($LogPath)) {
  $LogPath = Join-Path $LogsDirectory "foundation_freeze_$Stamp.log"
}
if ([string]::IsNullOrWhiteSpace($ManifestPath)) {
  $ManifestPath = Join-Path $LogsDirectory "foundation_freeze_$Stamp.json"
}
$LogPath = [System.IO.Path]::GetFullPath($LogPath)
$ManifestPath = [System.IO.Path]::GetFullPath($ManifestPath)
New-Item -ItemType Directory -Force -Path (Split-Path $LogPath -Parent) | Out-Null
New-Item -ItemType Directory -Force -Path (Split-Path $ManifestPath -Parent) | Out-Null
Set-Content -LiteralPath $LogPath -Value "" -Encoding UTF8

function Write-VerificationLine([string]$Text = "") {
  Write-Host $Text
  Add-Content -LiteralPath $LogPath -Value $Text -Encoding UTF8
}

function Get-GitText([string[]]$Arguments) {
  $SavedErrorActionPreference = $ErrorActionPreference
  try {
    # Windows PowerShell 5 wraps ordinary native stderr as ErrorRecord objects.
    # Keep the native exit code authoritative while still capturing that stream.
    $ErrorActionPreference = "Continue"
    $result = & git -C $GitRoot @Arguments 2>&1
    $ExitCode = $LASTEXITCODE
  } finally {
    $ErrorActionPreference = $SavedErrorActionPreference
  }
  if ($ExitCode -ne 0) {
    throw "git $($Arguments -join ' ') failed: $result"
  }
  return (($result | Out-String).Trim())
}

$Commit = Get-GitText @("rev-parse", "HEAD")
$Branch = Get-GitText @("rev-parse", "--abbrev-ref", "HEAD")
$StatusText = Get-GitText @("status", "--porcelain=v1", "--untracked-files=all")
$Dirty = ![string]::IsNullOrWhiteSpace($StatusText)
$Toolchain = (Get-Content -Raw (Join-Path $ProjectRoot "lean-toolchain")).Trim()
$SavedErrorActionPreference = $ErrorActionPreference
try {
  $ErrorActionPreference = "Continue"
  $LeanVersionOutput = & $Lake env lean --version 2>&1
  $LeanVersionExitCode = $LASTEXITCODE
  $LakeVersionOutput = & $Lake --version 2>&1
  $LakeVersionExitCode = $LASTEXITCODE
} finally {
  $ErrorActionPreference = $SavedErrorActionPreference
}
if ($LeanVersionExitCode -ne 0) { throw "Unable to query Lean version: $LeanVersionOutput" }
if ($LakeVersionExitCode -ne 0) { throw "Unable to query Lake version: $LakeVersionOutput" }
$LeanVersionLines = @($LeanVersionOutput | ForEach-Object { $_.ToString() })
$LeanVersion = @($LeanVersionLines | Where-Object { $_ -match '^Lean \(version ' } | Select-Object -Last 1)
if ($LeanVersion.Count -eq 0) { $LeanVersion = (($LeanVersionLines | Out-String).Trim()) }
else { $LeanVersion = $LeanVersion[0] }
$LakeVersion = (($LakeVersionOutput | ForEach-Object { $_.ToString() } | Out-String).Trim())
$VerifierHash = (Get-FileHash -Algorithm SHA256 -LiteralPath $PSCommandPath).Hash.ToLowerInvariant()
$ContractVersionPath = Join-Path $ProjectRoot "verification\PUBLICATION_CONTRACT_VERSION"
$ContractVersion = (Get-Content -Raw -LiteralPath $ContractVersionPath).Trim()

$Dependencies = @()
$LakeManifest = Join-Path $ProjectRoot "lake-manifest.json"
if (Test-Path -LiteralPath $LakeManifest) {
  $Manifest = Get-Content -Raw -LiteralPath $LakeManifest | ConvertFrom-Json
  foreach ($Package in $Manifest.packages) {
    $Dependencies += [ordered]@{
      name = $Package.name
      revision = if ($null -ne $Package.rev) { $Package.rev } else { "" }
      url = if ($null -ne $Package.url) { $Package.url } else { "" }
    }
  }
}

Write-VerificationLine "============================================================"
Write-VerificationLine "GM FOUNDATION FREEZE - CANONICAL VERIFIER"
Write-VerificationLine "============================================================"
Write-VerificationLine "Verifier version: $VerifierVersion"
Write-VerificationLine "Verifier SHA256: $VerifierHash"
Write-VerificationLine "Mode: $Mode"
Write-VerificationLine "Timestamp: $($Timestamp.ToString('o'))"
Write-VerificationLine "Timezone: $([System.TimeZoneInfo]::Local.Id)"
Write-VerificationLine "Git root: $GitRoot"
Write-VerificationLine "Project path: $ProjectRoot"
Write-VerificationLine "Commit: $Commit"
Write-VerificationLine "Branch: $Branch"
Write-VerificationLine "Working tree: $(if ($Dirty) { 'DIRTY' } else { 'CLEAN' })"
Write-VerificationLine "Toolchain: $Toolchain"
Write-VerificationLine "Lean: $LeanVersion"
Write-VerificationLine "Lake: $LakeVersion"
Write-VerificationLine "Publication contract: $ContractVersion"

$Failures = New-Object System.Collections.Generic.List[string]
$StageResults = New-Object System.Collections.Generic.List[object]

if ($Mode -eq "release" -and $Dirty) {
  $Failures.Add("release mode refuses a dirty working tree")
  Write-VerificationLine "FAIL [release provenance] working tree is dirty"
}

function Invoke-LakeStage([string]$Name, [string[]]$Arguments,
    [switch]$AllowAuditInfo, [switch]$AllowLintInfo) {
  Write-VerificationLine ""
  Write-VerificationLine "[$Name]"
  $StageOutput = New-Object System.Collections.Generic.List[string]
  Push-Location $ProjectRoot
  $SavedErrorActionPreference = $ErrorActionPreference
  try {
    # Dependency materialization and compiler progress may legitimately use native
    # stderr.  Capture it, and decide success from the exit code plus diagnostics.
    $ErrorActionPreference = "Continue"
    & $Lake @Arguments 2>&1 | ForEach-Object {
      $Line = $_.ToString()
      $StageOutput.Add($Line)
      Write-VerificationLine $Line
    }
    $ExitCode = $LASTEXITCODE
  } finally {
    $ErrorActionPreference = $SavedErrorActionPreference
    Pop-Location
  }

  $WarningLines = @($StageOutput | Where-Object { $_ -match "(^|:\s*)warning:" })
  $TacticInfoLines = @($StageOutput | Where-Object {
      $_ -match "Try this:" -or
      $_ -match "declaration uses 'sorry'" -or
      $_ -match "\binformational tactic diagnostic\b"
    })
  $BuiltInfoLines = @($StageOutput | Where-Object {
      $_ -match "Built\s+RiemannZeta.*informational diagnostic"
    })
  $LinterFailureLines = @($StageOutput | Where-Object {
      $_ -match "Found [1-9][0-9]* errors in .* declarations" -or
      $_ -match 'The `[^`]+` linter reports'
    })

  $StageFailed = $false
  if ($ExitCode -ne 0) { $StageFailed = $true }
  if ($WarningLines.Count -ne 0) { $StageFailed = $true }
  if ($TacticInfoLines.Count -ne 0) { $StageFailed = $true }
  if ($BuiltInfoLines.Count -ne 0) { $StageFailed = $true }
  if ($LinterFailureLines.Count -ne 0) { $StageFailed = $true }

  if ($StageFailed) {
    $Failures.Add($Name)
    Write-VerificationLine "FAIL: $Name (exit=$ExitCode warnings=$($WarningLines.Count) tactic-info=$($TacticInfoLines.Count) built-info=$($BuiltInfoLines.Count) linter=$($LinterFailureLines.Count))"
  } else {
    Write-VerificationLine "PASS: $Name (zero project warnings, tactic suggestions, and linter failures)"
  }
  $StageResults.Add([ordered]@{
      name = $Name
      command = "lake $($Arguments -join ' ')"
      exitCode = $ExitCode
      warnings = $WarningLines.Count
      tacticInfo = $TacticInfoLines.Count
      informationalBuilds = $BuiltInfoLines.Count
      linterFailures = $LinterFailureLines.Count
      passed = !$StageFailed
    })
}

function Get-LocalModuleImports([string]$FilePath) {
  $Names = New-Object System.Collections.Generic.List[string]
  foreach ($Line in Get-Content -LiteralPath $FilePath) {
    if ($Line -match "^\s*import\s+(.+?)\s*$") {
      $Tail = ($Matches[1] -replace "--.*$", "").Trim()
      foreach ($Name in ($Tail -split "\s+")) {
        if (![string]::IsNullOrWhiteSpace($Name)) { $Names.Add($Name) }
      }
    }
  }
  return $Names
}

function Test-ModuleClosure {
  Write-VerificationLine ""
  Write-VerificationLine "[Filesystem/import closure]"
  $LocalModules = @{}
  $RootFile = Join-Path $ProjectRoot "RiemannZeta.lean"
  $LocalModules["RiemannZeta"] = $RootFile
  $SourceRoot = Join-Path $ProjectRoot "RiemannZeta"
  foreach ($File in Get-ChildItem -LiteralPath $SourceRoot -Recurse -File -Filter "*.lean") {
    $Relative = $File.FullName.Substring($ProjectRoot.Length + 1)
    $Module = ($Relative -replace "\.lean$", "") -replace "[\\/]", "."
    $LocalModules[$Module] = $File.FullName
  }

  $Reachable = New-Object 'System.Collections.Generic.HashSet[string]'
  $Queue = New-Object 'System.Collections.Generic.Queue[string]'
  $Queue.Enqueue("RiemannZeta")
  while ($Queue.Count -gt 0) {
    $Module = $Queue.Dequeue()
    if (!$Reachable.Add($Module)) { continue }
    if (!$LocalModules.ContainsKey($Module)) { continue }
    foreach ($Import in Get-LocalModuleImports $LocalModules[$Module]) {
      if ($LocalModules.ContainsKey($Import) -and !$Reachable.Contains($Import)) {
        $Queue.Enqueue($Import)
      }
    }
  }

  $ExplicitRegression = @("RiemannZeta.Audit", "RiemannZeta.Lint")
  $Rows = New-Object System.Collections.Generic.List[object]
  $Unclassified = New-Object System.Collections.Generic.List[string]
  foreach ($Module in ($LocalModules.Keys | Where-Object { $_ -ne "RiemannZeta" } | Sort-Object)) {
    $Class = if ($Reachable.Contains($Module)) {
      "ROOT_GRAPH"
    } elseif ($ExplicitRegression -contains $Module) {
      "EXPLICIT_REGRESSION"
    } else {
      $Unclassified.Add($Module)
      "UNCLASSIFIED"
    }
    $Rows.Add([ordered]@{
        module = $Module
        path = $LocalModules[$Module].Substring($ProjectRoot.Length + 1)
        classification = $Class
      })
  }
  $script:ModuleClassification = $Rows
  $RootCount = @($Rows | Where-Object { $_.classification -eq "ROOT_GRAPH" }).Count
  $RegressionCount = @($Rows | Where-Object { $_.classification -eq "EXPLICIT_REGRESSION" }).Count
  Write-VerificationLine "ROOT_GRAPH=$RootCount EXPLICIT_REGRESSION=$RegressionCount EXCLUDED_WITH_REASON=0 UNCLASSIFIED=$($Unclassified.Count)"
  if ($Unclassified.Count -ne 0) {
    foreach ($Module in $Unclassified) { Write-VerificationLine "FAIL [unclassified module] $Module" }
    $Failures.Add("filesystem/import closure")
    return $false
  }
  Write-VerificationLine "PASS: every RiemannZeta/**/*.lean file has exactly one mechanical classification"
  return $true
}

function Test-ProhibitedProofText {
  Write-VerificationLine ""
  Write-VerificationLine "[Repository proof-integrity scans]"
  $LeanFiles = Get-ChildItem -LiteralPath $ProjectRoot -Recurse -File -Filter "*.lean" |
    Where-Object { $_.FullName -notmatch "[\\/]\.lake[\\/]" -and $_.FullName -notmatch "[\\/]\.git[\\/]" }
  $Scans = @(
    [ordered]@{ name = "sorry/admit/sorryAx"; pattern = "\b(sorry|admit)\b|sorryAx" },
    [ordered]@{ name = "project axiom/constant"; pattern = "(?m)^\s*(axiom|constant)\b" },
    [ordered]@{ name = "unsafe proof bypass"; pattern = "\b(native_decide|implemented_by|unsafe)\b" }
  )
  $Passed = $true
  foreach ($Scan in $Scans) {
    $Hits = New-Object System.Collections.Generic.List[string]
    foreach ($File in $LeanFiles) {
      $LineNumber = 0
      foreach ($Line in Get-Content -LiteralPath $File.FullName) {
        $LineNumber++
        if ($Line -match $Scan.pattern) {
          $Relative = $File.FullName.Substring($ProjectRoot.Length + 1)
          $Hits.Add("${Relative}:${LineNumber}:$Line")
        }
      }
    }
    if ($Hits.Count -eq 0) {
      Write-VerificationLine "PASS: $($Scan.name)"
    } else {
      $Passed = $false
      foreach ($Hit in $Hits) { Write-VerificationLine "FAIL [$($Scan.name)] $Hit" }
    }
  }
  if (!$Passed) { $Failures.Add("proof-integrity scans") }
  return $Passed
}

Test-ModuleClosure | Out-Null
Test-ProhibitedProofText | Out-Null
Invoke-LakeStage "Root/default production build" @("build", "RiemannZeta")
Invoke-LakeStage "Exact publication contract" @("env", "lean", "RiemannZeta/PublicationContract.lean")
Invoke-LakeStage "Retained regression TestExp" @("env", "lean", "TestExp.lean")
Invoke-LakeStage "Retained regression test_separated" @("env", "lean", "test_separated.lean")
Invoke-LakeStage "Transitive axiom and exact-output audit" @("env", "lean", "RiemannZeta/Audit.lean") -AllowAuditInfo
Invoke-LakeStage "Declaration linter gate" @("env", "lean", "RiemannZeta/Lint.lean") -AllowLintInfo

$FinalStatus = if ($Failures.Count -eq 0) { "PASS" } else { "FAIL" }
$LogHash = (Get-FileHash -Algorithm SHA256 -LiteralPath $LogPath).Hash.ToLowerInvariant()
$Result = [ordered]@{
  schemaVersion = 1
  verifierVersion = $VerifierVersion
  verifierSha256 = $VerifierHash
  publicationContractVersion = $ContractVersion
  mode = $Mode
  status = $FinalStatus
  timestamp = $Timestamp.ToString("o")
  timezone = [System.TimeZoneInfo]::Local.Id
  repositoryRoot = $GitRoot
  projectPath = $ProjectRoot
  git = [ordered]@{ commit = $Commit; branch = $Branch; dirty = $Dirty }
  toolchain = $Toolchain
  leanVersion = $LeanVersion
  lakeVersion = $LakeVersion
  dependencies = $Dependencies
  stages = $StageResults
  moduleClassification = $ModuleClassification
  failures = @($Failures)
  logPath = $LogPath
  logSha256BeforeFinalSummary = $LogHash
}
$Result | ConvertTo-Json -Depth 8 | Set-Content -LiteralPath $ManifestPath -Encoding UTF8

Write-VerificationLine ""
Write-VerificationLine "============================================================"
Write-VerificationLine "FINAL RESULT: $FinalStatus"
Write-VerificationLine "============================================================"
Write-VerificationLine "Commit: $Commit"
Write-VerificationLine "Working tree: $(if ($Dirty) { 'DIRTY' } else { 'CLEAN' })"
Write-VerificationLine "Log: $LogPath"
Write-VerificationLine "Manifest: $ManifestPath"
if ($Failures.Count -ne 0) {
  foreach ($Failure in $Failures) { Write-VerificationLine "FAILED: $Failure" }
  exit 1
}
exit 0
