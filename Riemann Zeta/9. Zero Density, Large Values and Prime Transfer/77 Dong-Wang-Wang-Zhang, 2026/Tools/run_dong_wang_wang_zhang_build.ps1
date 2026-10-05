Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'
$paperRoot = (Resolve-Path -LiteralPath (Join-Path $PSScriptRoot '..')).Path
$foundationRoot = [IO.Path]::GetFullPath((Join-Path $paperRoot '..\..'))
$logRoot = Join-Path $paperRoot 'logs'
New-Item -ItemType Directory -Path $logRoot -Force | Out-Null
$stamp = Get-Date -Format 'yyyyMMdd-HHmmss-fff'
$logPath = Join-Path $logRoot "dong-wang-wang-zhang-build-$stamp.log"
$resultCode = 1
$transcribing = $false

function Invoke-LeanGate {
    param([string]$Label, [string[]]$Arguments)
    Write-Output "STAGE: $Label"
    Push-Location -LiteralPath (Join-Path $paperRoot 'Extension')
    try {
        $savedPreference = $ErrorActionPreference
        try {
            $ErrorActionPreference = 'Continue'
            $output = @(& $lakeCommand.Source @Arguments 2>&1)
            $nativeExit = $LASTEXITCODE
        } finally { $ErrorActionPreference = $savedPreference }
        $output | ForEach-Object { Write-Output "$_" }
        if (@($output | Where-Object {
            $_ -is [System.Management.Automation.ErrorRecord] -and
            $_.FullyQualifiedErrorId -notin @('NativeCommandError', 'NativeCommandErrorMessage')
        }).Count -ne 0) { throw "$Label invocation failed" }
        if ($nativeExit -ne 0) { throw "$Label exited $nativeExit" }
        if (@($output | Where-Object {
            "$_" -match '(^|\s)(warning:|error:)|Try this:|Found [1-9][0-9]* errors'
        }).Count -ne 0) { throw "$Label emitted a prohibited Lean diagnostic" }
        Write-Output "PASS: $Label; exit 0; zero Lean diagnostics"
    } finally { Pop-Location }
}

try {
    Start-Transcript -LiteralPath $logPath | Out-Null
    $transcribing = $true
    Write-Output 'Dong-Wang-Wang-Zhang 2026: COMPLETE MODULE AND CONTRACT VERIFICATION'
    $config = Get-Content -LiteralPath (Join-Path $PSScriptRoot 'scaffold.json') -Raw -Encoding UTF8 | ConvertFrom-Json
    if ($config.mode -notin @('active-development', 'project-complete') -or $config.proofGatesTotal -ne 20) {
        throw 'Unexpected verification mode or acceptance contract.'
    }
    if (@(Compare-Object @('SemanticRegression', 'Audit') @($config.verificationModules)).Count -ne 0) {
        throw 'Both semantic regression and transitive audit modules are mandatory.'
    }
    $actual = @(Get-ChildItem -LiteralPath $paperRoot -Recurse -File -Force | ForEach-Object {
        $_.FullName.Substring($paperRoot.Length + 1).Replace('\', '/')
    } | Where-Object { -not $_.StartsWith('logs/') -and -not $_.StartsWith('Extension/.lake/') })
    if (@($config.requiredFiles | Select-Object -Unique).Count -ne $config.requiredFiles.Count) {
        throw 'Duplicate entry in scaffold inventory.'
    }
    $difference = @(Compare-Object -ReferenceObject @($config.requiredFiles) -DifferenceObject $actual)
    if ($difference.Count -ne 0) {
        $difference | Format-Table | Out-String | Write-Output
        throw 'Missing or unclassified scaffold file.'
    }
    Write-Output "INVENTORY PASS: $($actual.Count) classified source/package/documentation files."
    & (Join-Path $PSScriptRoot 'verify_sources.ps1')
    $toolchain = (Get-Content -LiteralPath (Join-Path $foundationRoot 'lean-toolchain') -Raw -Encoding UTF8).Trim()
    if ($toolchain -ne $config.foundation.toolchain) { throw 'Parent Lean toolchain differs from the planning baseline.' }
    $manifest = Get-Content -LiteralPath (Join-Path $foundationRoot 'lake-manifest.json') -Raw -Encoding UTF8 | ConvertFrom-Json
    foreach ($name in @('mathlib', 'PrimeNumberTheoremAnd')) {
        $packages = @($manifest.packages | Where-Object { $_.name -eq $name })
        if ($packages.Count -ne 1 -or $packages[0].rev -ne $config.foundation.$name) {
            throw "Parent dependency pin changed or ambiguous: $name"
        }
    }
    $extensionRoot = Join-Path $paperRoot 'Extension'
    if ((Get-Content -LiteralPath (Join-Path $extensionRoot 'lean-toolchain') -Raw).Trim() -ne $toolchain) {
        throw 'Extension toolchain differs from the foundation.'
    }
    $extensionManifest = Get-Content -LiteralPath (Join-Path $extensionRoot 'lake-manifest.json') -Raw -Encoding UTF8 | ConvertFrom-Json
    if ($extensionManifest.packages.Count -ne $manifest.packages.Count + 1) { throw 'Unexpected dependency graph size.' }
    foreach ($package in $manifest.packages) {
        $matches = @($extensionManifest.packages | Where-Object { $_.name -eq $package.name })
        if ($matches.Count -ne 1 -or $matches[0].type -ne $package.type -or
            $matches[0].rev -ne $package.rev -or $matches[0].url -ne $package.url) {
            throw "Extension dependency differs from foundation: $($package.name)"
        }
    }
    $foundationDependency = @($extensionManifest.packages | Where-Object { $_.name -eq 'RiemannZeta' })
    if ($foundationDependency.Count -ne 1 -or $foundationDependency[0].type -ne 'path' -or
        [IO.Path]::GetFullPath((Join-Path $extensionRoot $foundationDependency[0].dir)) -ne $foundationRoot) {
        throw 'Extension does not resolve the intended local foundation.'
    }
    Write-Output 'PINS PASS: single pinned foundation/extension graph; foundation BAT is a separate sequential gate.'

    $prefixModule = 'DongWangWangZhang2026'
    $classifiedLean = @('Extension/' + $prefixModule + '.lean')
    foreach ($module in @($config.productionModules) + @($config.verificationModules)) {
        $classifiedLean += 'Extension/' + $prefixModule + '/' + $module.Replace('.', '/') + '.lean'
    }
    if (@($classifiedLean | Select-Object -Unique).Count -ne $classifiedLean.Count -or
        @(Compare-Object $classifiedLean @($actual | Where-Object { $_ -match '\.lean$' })).Count -ne 0) {
        throw 'Missing, duplicate or unclassified Lean module.'
    }
    $pending = [Collections.Generic.Queue[string]]::new()
    $visited = [Collections.Generic.HashSet[string]]::new()
    $pending.Enqueue($prefixModule)
    while ($pending.Count -gt 0) {
        $module = $pending.Dequeue()
        if (-not $visited.Add($module)) { continue }
        $path = Join-Path $extensionRoot ($module.Replace('.', '/') + '.lean')
        $body = Get-Content -LiteralPath $path -Raw -Encoding UTF8
        foreach ($match in [regex]::Matches($body, '(?m)^import (DongWangWangZhang2026(?:\.[A-Za-z0-9_]+)+)\s*$')) {
            $pending.Enqueue($match.Groups[1].Value)
        }
    }
    $expectedGraph = @($prefixModule) + @($config.productionModules | ForEach-Object { "$prefixModule.$_" })
    if (@(Compare-Object $expectedGraph @($visited)).Count -ne 0) { throw 'Root import graph does not match all production modules.' }
    foreach ($path in $classifiedLean) {
        $body = Get-Content -LiteralPath (Join-Path $paperRoot $path) -Raw -Encoding UTF8
        if ($body -match '\b(sorry|admit|sorryAx|native_decide|implemented_by|unsafe)\b|(?m)^\s*(axiom|constant)\b') {
            throw "Proof-integrity scan rejected $path"
        }
    }
    Write-Output "COVERAGE PASS: $($config.productionModules.Count) production modules in root graph; $($config.verificationModules.Count) explicit verification modules; no excluded Lean source."
    $prefix = 'Dong-Wang-Wang-Zhang '
    $checklist = Get-Content -LiteralPath (Join-Path $paperRoot ($prefix + 'Checklist.md')) -Raw -Encoding UTF8
    $architecture = Get-Content -LiteralPath (Join-Path $paperRoot ($prefix + 'Architecture.md')) -Raw -Encoding UTF8
    $completeCount = 0
    for ($i = 1; $i -le 20; $i++) {
        $id = 'DWWZ-{0:00}' -f $i
        $statusRows = [regex]::Matches($checklist, ('(?m)^\| ' + $id + ' \| (OPEN|DONE) \|'))
        if ($statusRows.Count -ne 1) {
            throw "Checklist gate must occur once: $id"
        }
        $status = $statusRows[0].Groups[1].Value
        if ($status -eq 'DONE') { $completeCount++ }
        if ($architecture -notmatch ('G{0:00}\["{1}[^\r\n]*{2}' -f $i, $id, $status)) {
            throw "Architecture gate disagrees with checklist: $id"
        }
    }
    if ($completeCount -ne $config.proofGatesComplete) { throw 'Proof-count metadata drift.' }
    foreach ($doc in @('README.md', ($prefix + 'Research Agenda.md'), ($prefix + 'Checklist.md'), ($prefix + 'Architecture.md'))) {
        if ((Get-Content -LiteralPath (Join-Path $paperRoot $doc) -Raw -Encoding UTF8) -notmatch "$completeCount/20") {
            throw "Missing current proof-count disclosure: $doc"
        }
    }
    $prompt = Get-Content -LiteralPath (Join-Path $paperRoot ($prefix + 'Goal Prompt.md')) -Raw -Encoding UTF8
    $goalMarker = if ($config.mode -eq 'project-complete') { 'GOAL COMPLETE' } else { 'ACTIVE GOAL' }
    if ($config.mode -eq 'project-complete' -and $completeCount -ne 20) {
        throw 'Project-complete mode requires all twenty accepted gates.'
    }
    if ($config.mode -eq 'active-development' -and $completeCount -eq 20) {
        throw 'Twenty accepted gates require synchronized project-complete mode.'
    }
    foreach ($marker in @($goalMarker, 'run_dong_wang_wang_zhang_build.bat', 'run_lake_build.bat', 'push_to_github.bat', 'Recovery-record')) {
        if (-not $prompt.Contains($marker)) { throw "Goal prompt lost required boundary: $marker" }
    }
    $regression = Get-Content -LiteralPath (Join-Path $extensionRoot "$prefixModule/SemanticRegression.lean") -Raw -Encoding UTF8
    $audit = Get-Content -LiteralPath (Join-Path $extensionRoot "$prefixModule/Audit.lean") -Raw -Encoding UTF8
    foreach ($contract in @(
        @('exactTheoremOneSourceContract', 'large_zeta_sum_forces_zero_disk'),
        @('exactTheoremTwoSourceContract', 'local_zero_windows_force_zeta_sum_cancellation'),
        @('exactLargeCutoffSourceContract', 'exists_large_x_zeta_sum_bound')
    )) {
        if ($regression -notmatch ('(?m)^theorem ' + $contract[0] + ' :') -or
            -not $regression.Contains($contract[1]) -or
            -not $audit.Contains('SemanticRegression.' + $contract[0]) -or
            -not $audit.Contains($contract[1])) {
            throw "Missing required actual public-contract regression/audit: $($contract[0])"
        }
    }
    Write-Output 'CONTRACT COVERAGE PASS: both frozen main types and all-large-x source type are mandatory kernel-checked audit consumers.'
    $tex = Get-Content -LiteralPath (Join-Path $paperRoot 'Sources\DongWangWangZhang-v1-source\main.tex') -Raw -Encoding UTF8
    foreach ($label in @('thm:main', 'thm:corollary', 'lem:standard-mean', 'lem:t0', 'lem:zeta-crude', 'lem:zero-bound', 'lem:gaussian', 'lem:zero-sum-upper', 'prop:forcing', 'lem:large-x')) {
        if (-not $tex.Contains('\label{' + $label + '}')) { throw "Missing primary source label: $label" }
    }
    Write-Output "STATUS PASS: $completeCount/20 gates complete; mode $($config.mode); ten frozen source result labels present."
    $linkCount = 0
    foreach ($relative in @($actual | Where-Object { $_ -match '\.md$' })) {
        $doc = Get-Item -LiteralPath (Join-Path $paperRoot $relative)
        $body = Get-Content -LiteralPath $doc.FullName -Raw -Encoding UTF8
        foreach ($match in [regex]::Matches($body, '\[[^\]\r\n]*\]\(([^)\r\n]+)\)')) {
            $target = $match.Groups[1].Value.Trim('<', '>')
            if ($target -match '^(https?://|mailto:|#)') { continue }
            $target = [Uri]::UnescapeDataString(($target -split '#', 2)[0])
            if (-not (Test-Path -LiteralPath (Join-Path $doc.DirectoryName $target))) {
                throw "Broken local link in $($doc.Name): $target"
            }
            $linkCount++
        }
    }
    Write-Output "LOCAL LINKS PASS: $linkCount links. External URLs are not re-fetched offline."
    $lakeCommand = Get-Command lake -ErrorAction Stop
    if ([string]::IsNullOrWhiteSpace($env:ELAN_HOME)) {
        $elanCandidate = Split-Path -Parent (Split-Path -Parent $lakeCommand.Source)
        if (-not (Test-Path -LiteralPath (Join-Path $elanCandidate 'toolchains'))) { throw 'Cannot infer ELAN_HOME.' }
        $env:ELAN_HOME = $elanCandidate
    }
    $buildArguments = @('build', $prefixModule) + @($config.verificationModules | ForEach-Object { "$prefixModule.$_" })
    Invoke-LeanGate 'complete package and retained verification builds' $buildArguments
    foreach ($module in $config.verificationModules) {
        Invoke-LeanGate $module @('env', 'lean', ($prefixModule + '/' + $module.Replace('.', '/') + '.lean'))
    }
    if ($config.mode -eq 'project-complete') {
        Write-Output 'PROOF PASS - BOTH FROZEN MAIN CONTRACTS VERIFIED; 20/20 GATES'
    } else {
        Write-Output 'DEVELOPMENT PASS - BOTH MAIN CONTRACTS VERIFIED; RELEASE GATES OPEN'
    }
    Write-Output "Log: $logPath"
    $resultCode = 0
} catch {
    Write-Output "VERIFICATION FAIL: $($_.Exception.Message)"
    Write-Output "Log: $logPath"
} finally {
    if ($transcribing) { Stop-Transcript | Out-Null }
}
exit $resultCode
