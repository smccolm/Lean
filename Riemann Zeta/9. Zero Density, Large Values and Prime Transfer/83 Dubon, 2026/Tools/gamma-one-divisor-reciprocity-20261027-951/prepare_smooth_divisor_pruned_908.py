from pathlib import Path
import json,re,shutil
p=Path(r'E:\Lean\.tmp\dubon83')
cfg=json.loads((p/'source-gamma-one-smooth-divisor-probe-907.json').read_text(encoding='utf-8'))
defer={'SourceModularSmoothProjectiveRepresentatives':['projectionEquiv_fst','finite_projective_fibre'],'SourceSmoothModularGeometry':['finite_fibre']}
saved=p/'smooth-divisor-incidental-lemmas-deferred-908';saved.mkdir()
for m,names in defer.items():
 f=p/(m+'.lean');t=f.read_text(encoding='utf-8')
 (saved/(m+'.lean.txt')).write_bytes(f.read_bytes())
 for n in names:
  start=t.index('theorem '+n+' ')
  nxt=re.search(r'\n(?:(?:/--|theorem|def|end)\b)',t[start+1:])
  assert nxt,n
  stop=start+1+nxt.start()+1
  t=t[:start]+t[stop:]
 f.write_text(t,encoding='utf-8',newline='\n')
cfg['theorems']=[n for n in cfg['theorems'] if not any(n.rsplit('.',1)[1] in xs for xs in defer.values())]
cfg['queries']=cfg['theorems']+cfg['constructions']
for m in cfg['modules'][2:]:cfg['compileEvidence'][m]=m+'908a'
with (p/'source-gamma-one-smooth-divisor-908-compile-config.json').open('x',encoding='utf-8') as f:json.dump(cfg,f,indent=2)
ps="$ErrorActionPreference='Stop'\n$env:ELAN_HOME='C:\\Users\\Naraphim\\.elan'\n$env:LEAN_PATH='E:\\Lean\\.tmp\\dubon83'\nSet-Location -LiteralPath 'E:\\Lean\\Riemann Zeta\\9. Zero Density, Large Values and Prime Transfer\\83 Dubon, 2026\\Extension'\n"
ps+="$mods=@("+','.join("'"+m+"'" for m in cfg['modules'][2:])+")\n"
ps+=r"""foreach($m in $mods) {
 $src="E:\Lean\.tmp\dubon83\$m.lean"
 $out="E:\Lean\.tmp\dubon83\$m.olean"
 $log="E:\Lean\.tmp\dubon83\${m}908a.log"
 $ex="E:\Lean\.tmp\dubon83\${m}908a.exit"
 if((Test-Path -LiteralPath $log) -or (Test-Path -LiteralPath $ex)) {throw "Evidence exists: $m"}
 & 'C:\Users\Naraphim\.elan\bin\lake.exe' env lean -DautoImplicit=false --root 'E:\Lean\.tmp\dubon83' -o $out $src *> $log
 $rc=$LASTEXITCODE
 $rc | Out-File -LiteralPath $ex -Encoding ascii
 if($rc -ne 0 -or (Get-Item -LiteralPath $log).Length -ne 0) {Get-Content -LiteralPath $log -Encoding Unicode;throw "Compile failed: $m"}
 Write-Output "PASS $m"
}
"""
with (p/'compile_smooth_divisor_pruned_908.ps1').open('x',encoding='utf-8') as f:f.write(ps)
print('Deferred three unused lemmas; twelve affected modules queued; original source snapshots retained.')
