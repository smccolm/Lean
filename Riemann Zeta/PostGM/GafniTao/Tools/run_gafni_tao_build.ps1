param()

$ErrorActionPreference = 'Stop'

$programRoot = Split-Path -Parent $PSScriptRoot
$extensionRoot = Join-Path $programRoot 'Extension'
$cleanPntRoot = Join-Path $programRoot 'Dependencies\PrimeNumberTheoremAndClean'
$logRoot = Join-Path $programRoot 'logs'
$timestamp = Get-Date -Format 'yyyyMMdd_HHmmss'
$logPath = Join-Path $logRoot ("gafni_tao_release_{0}.log" -f $timestamp)
$env:ELAN_HOME = Join-Path $env:USERPROFILE '.elan'
$lake = Join-Path $env:ELAN_HOME 'bin\lake.exe'

New-Item -ItemType Directory -Force -Path $logRoot | Out-Null

$script:failed = $false

function Write-ReleaseLine {
  param([string]$Text)
  Write-Host $Text
  Add-Content -LiteralPath $logPath -Value $Text -Encoding UTF8
}

function Invoke-LoggedCommand {
  param(
    [string]$Name,
    [string]$WorkingDirectory,
    [string[]]$Arguments,
    [switch]$RejectDiagnostics
  )

  Write-ReleaseLine ""
  Write-ReleaseLine ("[{0}]" -f $Name)
  $stageLog = Join-Path $logRoot (".{0}_{1}.tmp" -f $timestamp, ($Name -replace '[^A-Za-z0-9_-]', '_'))
  Push-Location $WorkingDirectory
  $previousErrorActionPreference = $ErrorActionPreference
  try {
    # Windows PowerShell wraps native stderr as non-terminating ErrorRecord
    # objects.  Capture those verbatim and judge the native exit code and
    # diagnostics below instead of allowing the host preference to abort the
    # release runner before it can print an honest stage verdict.
    $ErrorActionPreference = 'Continue'
    & $lake @Arguments 2>&1 | Tee-Object -FilePath $stageLog
    $exitCode = $LASTEXITCODE
  } finally {
    $ErrorActionPreference = $previousErrorActionPreference
    Pop-Location
  }
  Get-Content -LiteralPath $stageLog | Add-Content -LiteralPath $logPath -Encoding UTF8
  $stageText = Get-Content -LiteralPath $stageLog
  Remove-Item -LiteralPath $stageLog

  $diagnostics = @()
  if ($RejectDiagnostics) {
    $diagnostics = @($stageText | Where-Object {
      $_ -match '(^|\s)warning:' -or $_ -match '^info: .*\.lean:\d+:\d+:' -or $_ -match 'Try this:'
    })
  }

  if ($exitCode -ne 0) {
    Write-ReleaseLine ("FAIL: {0} exited with code {1}." -f $Name, $exitCode)
    $script:failed = $true
  } elseif ($diagnostics.Count -ne 0) {
    Write-ReleaseLine ("FAIL: {0} emitted {1} Lean warning/linter diagnostic line(s)." -f $Name, $diagnostics.Count)
    $script:failed = $true
  } else {
    Write-ReleaseLine ("PASS: {0}" -f $Name)
  }
}

function Test-CleanPntClosure {
  Write-ReleaseLine ""
  Write-ReleaseLine '[Warning-free pinned PNT+ closure verification]'
  $manifest = Join-Path $cleanPntRoot 'SOURCE_SHA256SUMS.txt'
  $bad = @()
  $entries = @()

  if (-not (Test-Path -LiteralPath $manifest)) {
    $bad += 'missing clean PNT+ source manifest'
  } else {
    foreach ($line in Get-Content -LiteralPath $manifest) {
      if ($line -match '^([0-9A-Fa-f]{64})\s{2}([0-9A-Fa-f]{64})\s{2}(.+)$') {
        $entries += [PSCustomObject]@{
          Upstream = $Matches[1].ToUpperInvariant()
          Retained = $Matches[2].ToUpperInvariant()
          Name = $Matches[3]
        }
      }
    }
  }

  if ($entries.Count -ne 83) {
    $bad += "clean PNT+ manifest has $($entries.Count) entries; expected 83"
  }

  $changed = @($entries | Where-Object { $_.Upstream -ne $_.Retained })
  if ($changed.Count -ne 1 -or $changed[0].Name -ne 'PrimeNumberTheoremAnd/Wiener.lean' -or
      $changed[0].Upstream -ne '018B8E199027B5DE07C1CB5BE66F4F4E2B36E9E872B308B576437401DA60CE67' -or
      $changed[0].Retained -ne 'E55EBC39A66F5C2C59D8F62B3328A0D98876DCC85D6915C80805B05A41504F3D') {
    $bad += 'clean PNT+ divergence is not exactly the recorded Wiener.lean edit'
  }

  foreach ($entry in $entries) {
    $path = Join-Path $cleanPntRoot $entry.Name
    if (-not (Test-Path -LiteralPath $path)) {
      $bad += "missing clean PNT+ source: $($entry.Name)"
    } else {
      $actual = (Get-FileHash -LiteralPath $path -Algorithm SHA256).Hash.ToUpperInvariant()
      if ($actual -ne $entry.Retained) {
        $bad += "clean PNT+ retained hash mismatch: $($entry.Name)"
      }
    }
  }

  $leanFiles = @(Get-ChildItem -LiteralPath $cleanPntRoot -Filter '*.lean' -Recurse |
    Where-Object { $_.FullName -notmatch '[\\/]\.lake[\\/]' })
  if ($leanFiles.Count -ne 84) {
    $bad += "clean PNT+ package has $($leanFiles.Count) Lean files; expected 84 (root plus closure)"
  }

  $wiener = Join-Path $cleanPntRoot 'PrimeNumberTheoremAnd\Wiener.lean'
  if (Test-Path -LiteralPath $wiener) {
    $removedNames = Select-String -LiteralPath $wiener -Pattern '^\s*(lemma|theorem|def|abbrev|structure)\s+(prelim_decay_2|AbsolutelyContinuous|prelim_decay_3|decay_alt)\b'
    if ($removedNames.Count -ne 0) {
      $bad += 'removed unreachable Wiener declarations reappeared'
    }
  }

  $rootModule = Join-Path $cleanPntRoot 'PrimeNumberTheoremAnd.lean'
  if (Test-Path -LiteralPath $rootModule) {
    $rootLines = @(Get-Content -LiteralPath $rootModule | Where-Object { $_.Trim().Length -ne 0 })
    if ($rootLines.Count -ne 1 -or $rootLines[0].Trim() -ne 'import PrimeNumberTheoremAnd.Consequences') {
      $bad += 'clean PNT+ root is not the exact one-import Consequences root'
    }
  }

  $pntToolchain = Join-Path $cleanPntRoot 'lean-toolchain'
  if (-not (Test-Path -LiteralPath $pntToolchain) -or
      (Get-Content -Raw -LiteralPath $pntToolchain).Trim() -ne 'leanprover/lean4:v4.30.0') {
    $bad += 'clean PNT+ package has the wrong Lean toolchain pin'
  }

  $extensionManifest = Join-Path $extensionRoot 'lake-manifest.json'
  if (-not (Test-Path -LiteralPath $extensionManifest)) {
    $bad += 'missing extension Lake manifest'
  } else {
    $resolved = Get-Content -Raw -LiteralPath $extensionManifest | ConvertFrom-Json
    $pntPackages = @($resolved.packages | Where-Object { $_.name -eq 'PrimeNumberTheoremAnd' })
    if ($pntPackages.Count -ne 1 -or $pntPackages[0].type -ne 'path' -or
        $pntPackages[0].dir -ne '../Dependencies/PrimeNumberTheoremAndClean') {
      $bad += 'extension manifest does not resolve PNT+ to the audited local closure'
    }
  }

  $pntManifest = Join-Path $cleanPntRoot 'lake-manifest.json'
  if (-not (Test-Path -LiteralPath $pntManifest)) {
    $bad += 'missing clean PNT+ Lake manifest'
  } else {
    $pntResolved = Get-Content -Raw -LiteralPath $pntManifest | ConvertFrom-Json
    $mathlibPackages = @($pntResolved.packages | Where-Object { $_.name -eq 'mathlib' })
    $architectPackages = @($pntResolved.packages | Where-Object { $_.name -eq 'LeanArchitect' })
    if ($mathlibPackages.Count -ne 1 -or
        $mathlibPackages[0].rev -ne 'c5ea00351c28e24afc9f0f84379aa41082b1188f') {
      $bad += 'clean PNT+ manifest has the wrong Mathlib revision'
    }
    if ($architectPackages.Count -ne 1 -or
        $architectPackages[0].rev -ne 'b72ae37b08d264cf371f164f4ba60c5257c17727') {
      $bad += 'clean PNT+ manifest has the wrong LeanArchitect revision'
    }
  }

  if ($bad.Count -ne 0) {
    foreach ($failure in $bad) { Write-ReleaseLine "FAIL: $failure" }
    $script:failed = $true
  } else {
    Write-ReleaseLine 'PASS: exact 83-file PNT+ closure retained; 82 files are byte-identical and the recorded unreachable Wiener block is the sole edit.'
  }
}

function Test-SourceHashes {
  Write-ReleaseLine ""
  Write-ReleaseLine '[Pinned source SHA-256 verification]'
  $manifest = Join-Path $programRoot 'Sources\SHA256SUMS.txt'
  $bad = @()
  foreach ($line in Get-Content -LiteralPath $manifest) {
    if ($line -match '^([0-9A-Fa-f]{64})\s{2}(.+)$') {
      $expected = $Matches[1].ToUpperInvariant()
      $name = $Matches[2]
      $path = Join-Path (Split-Path -Parent $manifest) $name
      if (-not (Test-Path -LiteralPath $path)) {
        $bad += "missing: $name"
      } else {
        $actual = (Get-FileHash -LiteralPath $path -Algorithm SHA256).Hash.ToUpperInvariant()
        if ($actual -ne $expected) {
          $bad += "hash mismatch: $name"
        }
      }
    }
  }

  $foundationManifest = Join-Path $extensionRoot 'FrozenFoundation\SHA256SUMS.txt'
  foreach ($line in Get-Content -LiteralPath $foundationManifest) {
    if ($line -match '^([0-9A-Fa-f]{64})\s{2}(.+)$') {
      $expected = $Matches[1].ToUpperInvariant()
      $name = $Matches[2]
      $path = Join-Path (Split-Path -Parent $foundationManifest) $name
      if (-not (Test-Path -LiteralPath $path)) {
        $bad += "missing frozen foundation artifact: $name"
      } else {
        $actual = (Get-FileHash -LiteralPath $path -Algorithm SHA256).Hash.ToUpperInvariant()
        if ($actual -ne $expected) {
          $bad += "frozen foundation hash mismatch: $name"
        }
      }
    }
  }

  if ($bad.Count -ne 0) {
    foreach ($failure in $bad) { Write-ReleaseLine "FAIL: $failure" }
    $script:failed = $true
  } else {
    Write-ReleaseLine 'PASS: all downloaded sources and the frozen-foundation archive match their manifests.'
  }
}

function Test-ForbiddenLeanTokens {
  Write-ReleaseLine ""
  Write-ReleaseLine '[Forbidden Lean token scan]'
  $targets = @(
    (Join-Path $extensionRoot 'GafniTao'),
    (Join-Path $extensionRoot 'GafniTao.lean'),
    (Join-Path $cleanPntRoot 'PrimeNumberTheoremAnd'),
    (Join-Path $cleanPntRoot 'PrimeNumberTheoremAnd.lean')
  )
  $patterns = @(
    '\b(sorry|admit)\b|sorryAx',
    '^\s*(axiom|constant)\b',
    '\b(native_decide|implemented_by|unsafe)\b'
  )
  $matches = @()

  # Ripgrep is convenient but is not part of Lean or Windows PowerShell.  Keep
  # the human-facing verifier runnable on a clean machine by falling back to
  # Select-String over the exact same set of Lean source files.
  $rgCommand = Get-Command -Name 'rg' -CommandType Application -ErrorAction SilentlyContinue
  if ($null -ne $rgCommand) {
    foreach ($pattern in $patterns) {
      & $rgCommand.Source -n --glob '*.lean' $pattern @targets 2>&1 |
        ForEach-Object { $matches += $_.ToString() }
      if ($LASTEXITCODE -gt 1) {
        Write-ReleaseLine ("FAIL: rg failed while scanning pattern {0}." -f $pattern)
        $script:failed = $true
      }
    }
  } else {
    Write-ReleaseLine 'ripgrep was not found; using the built-in PowerShell scanner.'
    $leanFiles = @()
    foreach ($target in $targets) {
      if (Test-Path -LiteralPath $target -PathType Leaf) {
        if ([System.IO.Path]::GetExtension($target) -eq '.lean') {
          $leanFiles += (Get-Item -LiteralPath $target)
        }
      } elseif (Test-Path -LiteralPath $target -PathType Container) {
        $leanFiles += @(Get-ChildItem -LiteralPath $target -Filter '*.lean' -File -Recurse)
      } else {
        Write-ReleaseLine ("FAIL: forbidden-token scan target is missing: {0}" -f $target)
        $script:failed = $true
      }
    }
    $leanFiles = @($leanFiles | Sort-Object -Property FullName -Unique)
    try {
      foreach ($pattern in $patterns) {
        foreach ($file in $leanFiles) {
          Select-String -LiteralPath $file.FullName -Pattern $pattern | ForEach-Object {
            $matches += ("{0}:{1}:{2}" -f $_.Path, $_.LineNumber, $_.Line)
          }
        }
      }
    } catch {
      Write-ReleaseLine ("FAIL: built-in PowerShell forbidden-token scan failed: {0}" -f $_.Exception.Message)
      $script:failed = $true
    }
  }
  if ($matches.Count -ne 0) {
    foreach ($match in $matches) { Write-ReleaseLine $match }
    Write-ReleaseLine ("FAIL: forbidden-token scan found {0} match(es)." -f $matches.Count)
    $script:failed = $true
  } else {
    Write-ReleaseLine 'PASS: no forbidden Lean proof shortcut or project postulate was found.'
  }
}

Write-ReleaseLine 'Gafni-Tao isolated release verification'
Write-ReleaseLine ("Started: {0}" -f (Get-Date -Format 'yyyy-MM-dd HH:mm:ss K'))
Write-ReleaseLine 'Frozen GM tag: gm-foundation-freeze-v1.0.1'
Write-ReleaseLine 'Frozen GM commit: 2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be'
Write-ReleaseLine 'Lean toolchain: leanprover/lean4:v4.30.0'

if (-not (Test-Path -LiteralPath $lake)) {
  Write-ReleaseLine "FAIL: lake executable not found at $lake"
  exit 1
}

Test-SourceHashes
Test-CleanPntClosure
Invoke-LoggedCommand -Name 'Warning-free pinned PNT+ build' -WorkingDirectory $cleanPntRoot -Arguments @('build', 'PrimeNumberTheoremAnd') -RejectDiagnostics
Invoke-LoggedCommand -Name 'Root production build' -WorkingDirectory $extensionRoot -Arguments @('build', 'GafniTao') -RejectDiagnostics
Invoke-LoggedCommand -Name 'Central axiom audit' -WorkingDirectory $extensionRoot -Arguments @('env', 'lean', 'GafniTao\Audit.lean')
Test-ForbiddenLeanTokens

Write-ReleaseLine ""
Write-ReleaseLine 'FINAL RESULT'
if ($script:failed) {
  Write-ReleaseLine 'FAIL: at least one release verification gate failed; no complete-release claim is justified.'
  Write-ReleaseLine ("Log saved to: {0}" -f $logPath)
  exit 1
}

Write-ReleaseLine 'PASS: clean PNT+ closure, root build, zero-diagnostic gate, source hashes, axiom audit, and integrity scans all passed.'
Write-ReleaseLine ("Finished: {0}" -f (Get-Date -Format 'yyyy-MM-dd HH:mm:ss K'))
Write-ReleaseLine ("Log saved to: {0}" -f $logPath)
exit 0
