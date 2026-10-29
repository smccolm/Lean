$ErrorActionPreference = 'Stop'
& 'E:\Lean\.tmp\dubon83\run_scratch_module_1433.ps1' -Name 'SourceIntegralSlashCoefficientLocalization1764a'
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
& 'E:\Lean\.tmp\dubon83\run_scratch_module_1433.ps1' -Name 'SourceIntegralSlashCoefficientReduction1764a'
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
& 'E:\Lean\.tmp\dubon83\run_scratch_module_1433.ps1' -Name 'SourceIntegralSlashReducedSeries1764a'
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
& 'E:\Lean\.tmp\dubon83\run_scratch_module_1433.ps1' -Name 'SourceIntegralSlashReducedScaling1764a'
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
& 'E:\Lean\.tmp\dubon83\run_scratch_module_1433.ps1' -Name 'SourceIntegralSlashReducedZero1764a'
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
& 'E:\Lean\.tmp\dubon83\run_scratch_module_1433.ps1' -Name 'SourceIntegralSlashReducedOperations1764a'
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
& 'E:\Lean\.tmp\dubon83\run_scratch_module_1433.ps1' -Name 'SourceIntegralSlashReducedSums1764a'
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
& 'E:\Lean\.tmp\dubon83\run_scratch_module_1433.ps1' -Name 'SourceIntegralSlashLinearRelation1764a'
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
python -X utf8 'E:\Lean\.tmp\dubon83\prepare_integral_slash_chart_relations_preflight_1764.py'
if ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
& 'E:\Lean\.tmp\dubon83\audit_integral_slash_chart_relations_preflight_1764.ps1'
exit $LASTEXITCODE
