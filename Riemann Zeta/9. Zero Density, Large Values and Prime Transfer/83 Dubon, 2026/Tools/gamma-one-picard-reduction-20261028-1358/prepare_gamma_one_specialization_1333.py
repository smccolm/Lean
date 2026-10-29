from pathlib import Path
import json

p = Path(__file__).parent
versions = {
    'SourceGammaOneResidueGeometry': '1327b',
    'SourceCurveSeparatingGenusMaximum': '1328a',
    'SourceReductionGenusPoleLifting': '1329c',
    'SourceReductionGenusIntegralCharts': '1330c',
    'SourceGammaOneGenusSpecialization': '1331d',
    'SourceGammaOneOriginalSpecialization': '1332b',
}
for name, version in versions.items():
    stem = name + version
    evidence = stem + ('-run3' if stem == 'unused' else '')
    assert (p / (evidence + '.exit')).read_text().strip() == '0'
    assert (p / (evidence + '.log')).stat().st_size == 0
    src = (p / (stem + '.lean')).read_text(encoding='utf-8')
    for other, suffix in versions.items():
        src = src.replace('import ' + other + suffix + '\n', 'import ' + other + '\n')
    target = p / (name + '.lean')
    assert not target.exists(), target
    target.write_text(src, encoding='utf-8')

manifest = p / 'gamma-one-specialization-versions-1333.json'
assert not manifest.exists()
manifest.write_text(json.dumps(versions, indent=2) + '\n', encoding='utf-8')
runner = p / 'build_gamma_one_specialization_1333.ps1'
assert not runner.exists()
runner.write_text('''$ErrorActionPreference='Stop'
$env:ELAN_HOME='C:\\Users\\Naraphim\\.elan'
$env:LEAN_PATH='E:\\Lean\\.tmp\\dubon83'
Set-Location -LiteralPath 'E:\\Lean\\Riemann Zeta\\9. Zero Density, Large Values and Prime Transfer\\83 Dubon, 2026\\Extension'
$names=@(''' + ','.join("'" + n + "'" for n in versions) + ''')
foreach($n in $names){
 $base="E:\\Lean\\.tmp\\dubon83\\$n"
 $ev=$base+'-1333'
 if(Test-Path -LiteralPath "$ev.log"){throw "Evidence exists: $ev"}
 & 'C:\\Users\\Naraphim\\.elan\\bin\\lake.exe' env lean -DautoImplicit=false -R 'E:\\Lean\\.tmp\\dubon83' -o "$base.olean" "$base.lean" *> "$ev.log"
 $rc=$LASTEXITCODE
 $rc | Out-File -LiteralPath "$ev.exit" -Encoding ascii
 if($rc -ne 0 -or (Select-String -LiteralPath "$ev.log" -Pattern 'warning:|error(?:\\(|:)|PANIC|Try this:|sorryAx|Found [1-9]')){
  Get-Content -LiteralPath "$ev.log" -Encoding Unicode -Tail 30
  exit 1
 }
 Write-Output "PASS: $n"
}
''', encoding='utf-8-sig')
print(json.dumps(dict(modules=list(versions), runner=str(runner))))
