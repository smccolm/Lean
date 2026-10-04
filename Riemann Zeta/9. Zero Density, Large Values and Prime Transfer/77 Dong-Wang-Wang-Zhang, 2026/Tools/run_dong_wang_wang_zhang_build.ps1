Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'
$paperRoot = (Resolve-Path -LiteralPath (Join-Path $PSScriptRoot '..')).Path
$foundationRoot = [IO.Path]::GetFullPath((Join-Path $paperRoot '..\..'))
$logRoot = Join-Path $paperRoot 'logs'
New-Item -ItemType Directory -Path $logRoot -Force | Out-Null
$stamp = Get-Date -Format 'yyyyMMdd-HHmmss-fff'
$logPath = Join-Path $logRoot "dong-wang-wang-zhang-scaffold-$stamp.log"
$resultCode = 1
$transcribing = $false
try {
    Start-Transcript -LiteralPath $logPath | Out-Null
    $transcribing = $true
    Write-Output 'Dong-Wang-Wang-Zhang 2026: PLANNING SCAFFOLD ONLY'
    Write-Output 'LEAN PROOF BUILD: NOT STARTED. No Lake invocation or goal activation.'
    $config = Get-Content -LiteralPath (Join-Path $PSScriptRoot 'scaffold.json') -Raw -Encoding UTF8 | ConvertFrom-Json
    if ($config.mode -ne 'planning-only' -or $config.proofGatesComplete -ne 0 -or $config.proofGatesTotal -ne 20) {
        throw 'Scaffold mode/status changed: implement and audit a real proof runner before changing modes.'
    }
    $actual = @(Get-ChildItem -LiteralPath $paperRoot -Recurse -File -Force | ForEach-Object {
        $_.FullName.Substring($paperRoot.Length + 1).Replace('\', '/')
    } | Where-Object { -not $_.StartsWith('logs/') })
    if (@($config.requiredFiles | Select-Object -Unique).Count -ne $config.requiredFiles.Count) {
        throw 'Duplicate entry in scaffold inventory.'
    }
    $difference = @(Compare-Object -ReferenceObject @($config.requiredFiles) -DifferenceObject $actual)
    if ($difference.Count -ne 0) {
        $difference | Format-Table | Out-String | Write-Output
        throw 'Missing or unclassified scaffold file.'
    }
    if (@($actual | Where-Object { $_ -match '\.lean$|(^|/)(lakefile\.(toml|lean)|lake-manifest\.json|lean-toolchain)$' }).Count -ne 0) {
        throw 'Lean/package files are forbidden in planning mode; no placeholder proof package is accepted.'
    }
    Write-Output "INVENTORY PASS: $($actual.Count) files; no Lean conversion."
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
    Write-Output 'PARENT PINS PASS: baseline observed, not rebuilt by this scaffold runner.'
    $prefix = 'Dong-Wang-Wang-Zhang '
    $checklist = Get-Content -LiteralPath (Join-Path $paperRoot ($prefix + 'Checklist.md')) -Raw -Encoding UTF8
    $architecture = Get-Content -LiteralPath (Join-Path $paperRoot ($prefix + 'Architecture.md')) -Raw -Encoding UTF8
    for ($i = 1; $i -le 20; $i++) {
        $id = 'DWWZ-{0:00}' -f $i
        if ([regex]::Matches($checklist, ('(?m)^\| ' + $id + ' \| OPEN \|')).Count -ne 1) {
            throw "Checklist gate must occur once and remain OPEN: $id"
        }
        if ($architecture -notmatch ('G{0:00}\["{1}[^\r\n]*OPEN' -f $i, $id)) {
            throw "Architecture gate must remain OPEN: $id"
        }
    }
    foreach ($doc in @('README.md', ($prefix + 'Research Agenda.md'), ($prefix + 'Checklist.md'), ($prefix + 'Architecture.md'))) {
        if ((Get-Content -LiteralPath (Join-Path $paperRoot $doc) -Raw -Encoding UTF8) -notmatch '0/20') {
            throw "Missing planning proof-count disclosure: $doc"
        }
    }
    $prompt = Get-Content -LiteralPath (Join-Path $paperRoot ($prefix + 'Goal Prompt.md')) -Raw -Encoding UTF8
    foreach ($marker in @('INACTIVE TEMPLATE', 'run_dong_wang_wang_zhang_build.bat', 'run_lake_build.bat', 'Recovery-record')) {
        if (-not $prompt.Contains($marker)) { throw "Goal prompt lost required boundary: $marker" }
    }
    $tex = Get-Content -LiteralPath (Join-Path $paperRoot 'Sources\DongWangWangZhang-v1-source\main.tex') -Raw -Encoding UTF8
    foreach ($label in @('thm:main', 'thm:corollary', 'lem:standard-mean', 'lem:t0', 'lem:zeta-crude', 'lem:zero-bound', 'lem:gaussian', 'lem:zero-sum-upper', 'prop:forcing', 'lem:large-x')) {
        if (-not $tex.Contains('\label{' + $label + '}')) { throw "Missing primary source label: $label" }
    }
    Write-Output 'STATUS PASS: 20/20 gates OPEN; inactive prompt; ten source result labels present.'
    $linkCount = 0
    foreach ($doc in Get-ChildItem -LiteralPath $paperRoot -Recurse -Filter '*.md' -File) {
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
    Write-Output 'SCAFFOLD PASS - NOT A LEAN PROOF PASS'
    Write-Output "Log: $logPath"
    $resultCode = 0
} catch {
    Write-Output "SCAFFOLD FAIL: $($_.Exception.Message)"
    Write-Output "Log: $logPath"
} finally {
    if ($transcribing) { Stop-Transcript | Out-Null }
}
exit $resultCode
