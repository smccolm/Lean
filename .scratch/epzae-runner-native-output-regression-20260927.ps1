$ErrorActionPreference = 'Stop'
$runnerPath = 'E:/Lean/Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/63 Tao-Trudgian-Yang, 2025/Tools/run_tao_trudgian_yang_build.ps1'
$tokens = $null
$parseErrors = $null
$syntax = [System.Management.Automation.Language.Parser]::ParseFile($runnerPath, [ref]$tokens, [ref]$parseErrors)
if ($parseErrors.Count) { throw 'Runner parsing failed.' }
$gate = $syntax.Find({ param($node) $node -is [System.Management.Automation.Language.FunctionDefinitionAst] -and $node.Name -eq 'Invoke-LeanGate' }, $true)
. ([scriptblock]::Create($gate.Extent.Text))
$nativeShell = Join-Path $PSHOME 'powershell.exe'
$cases = @(
    @{Label='native exit failure'; Code="[Console]::Out.WriteLine('visible stdout marker'); [Console]::Error.WriteLine('visible stderr marker'); exit 7"; Failure='failed with exit code 7'},
    @{Label='zero-exit warning failure'; Code="[Console]::Out.WriteLine('warning: intentional gate fixture'); exit 0"; Failure='emitted 1 Lean warning'},
    @{Label='native stderr warning failure'; Code="[Console]::Error.WriteLine('warning: intentional stderr fixture'); exit 0"; Failure='emitted 1 Lean warning'},
    @{Label='clean pass'; Code="[Console]::Out.WriteLine('clean fixture'); exit 0"; Failure=$null}
)
foreach ($case in $cases) {
    $caught = $null
    try {
        Invoke-LeanGate -Label $case.Label -WorkingDirectory 'E:/Lean' -Executable $nativeShell -Arguments @('-NoProfile','-Command',$case.Code)
    } catch { $caught = $_.Exception.Message }
    if ($case.Failure) {
        if (!$caught -or !$caught.Contains($case.Failure)) { throw "Wrong failure: $caught" }
    } elseif ($caught) { throw $caught }
    if ($ErrorActionPreference -ne 'Stop') { throw 'Error preference leaked.' }
    Write-Host "REGRESSION PASS: $($case.Label)"
}
$caught = $null
try {
    Invoke-LeanGate -Label 'missing executable failure' -WorkingDirectory 'E:/Lean' -Executable 'E:/Lean/.scratch/intentionally-nonexistent-gate-executable.exe' -Arguments @('test')
} catch { $caught = $_.Exception.Message }
if (!$caught -or
    !($caught.Contains('PowerShell invocation error') -or
      ($caught.Contains('intentionally-nonexistent-gate-executable.exe') -and $caught.Contains('not recognized')))) {
    throw "Wrong missing-executable failure: $caught"
}
if ($ErrorActionPreference -ne 'Stop') { throw 'Error preference leaked.' }
Write-Host 'REGRESSION PASS: missing executable failure'
