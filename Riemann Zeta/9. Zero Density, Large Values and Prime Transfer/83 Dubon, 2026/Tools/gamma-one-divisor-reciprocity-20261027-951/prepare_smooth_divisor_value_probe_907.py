from pathlib import Path
import json,re
p=Path(r'E:\Lean\.tmp\dubon83')
pairs=[
('SourceSmoothLocalModelRegularization','892a'),('SourceSmoothLocalModelProducts','892a'),
('SourceModularSmoothProjectiveRepresentatives','895b'),('SourceSmoothModularGeometry','896b'),
('SourceSmoothProjectiveOrbitSum','897a'),('SourceSmoothDivisorOrbitData','898b'),
('SourceSmoothModularLogDerivative','899c'),('SourceSmoothDivisorProduct','900b'),
('SourceSmoothDivisorLocalProduct','901b'),('SourceSmoothDivisorLocalOrders','902a'),
('SourceSmoothDivisorInvarianceCusps','903a'),('SourceSmoothDivisorLogDerivative','904b'),
('SourceSmoothInvariantComparison','905a'),('SourceGammaOneSmoothDivisorComparison','906a')]
mods=[m for m,e in pairs]; ths=[];defs=[];structs=[]
for m,e in pairs:
 f=p/(m+'.lean'); t=f.read_text(encoding='utf-8')
 assert (p/(m+e+'.exit')).read_text().strip()=='0' and (p/(m+e+'.log')).stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 ns=[]
 for line in t.splitlines():
  if line.startswith('namespace '): ns.append(line.split()[1])
  if line.startswith('end ') and ns and line.split()[1]==ns[-1]: ns.pop()
  hit=re.match(r'^(?:noncomputable |scoped )?(theorem|def|instance|structure) (\S+)',line)
  if hit:
   kind,n=hit.groups(); name='.'.join(ns+[n])
   (ths if kind=='theorem' else structs if kind=='structure' else defs).append(name)
closure=list(mods)
for cfg in ['source-complex-dipole-1-audit-config.json','source-gamma-one-smooth-partition-1b-audit-config.json','source-gamma-one-petersson-smooth-limit-1-audit-config.json']:
 d=json.loads((p/cfg).read_text(encoding='utf-8'))
 closure+=d.get('scratchImportClosure',d['modules'])
closure=list(dict.fromkeys(closure))
cfg=dict(modules=mods,theorems=ths,constructions=defs+structs,queries=ths+defs+structs,compileEvidence={m:m+e for m,e in pairs},scratchImportClosure=closure,roots=['Dubon2026.SourceFunctionField.GammaOne.exists_original_divisor_smooth_comparison'])
with (p/'source-gamma-one-smooth-divisor-probe-907.json').open('x',encoding='utf-8') as f:json.dump(cfg,f,indent=2)
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
s=(p/'SourceComplexDipoleDependencyAudit1.lean').read_text(encoding='utf-8')
s='import SourceGammaOneSmoothDivisorComparison\nimport Mathlib.Tactic\n\nopen Lean\n\n'+s[s.index('private def runPlanarPairingDependencyAudit'):]
for k,v in [('roots',cfg['roots']),('localModules',closure),('required',ths+defs+structs)]:
 s=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),s)
s=s[:s.index('  unless missing.isEmpty')]+'  logInfo m!"VALUE-CLOSURE PROBE: {required.size} candidates; outside closure: {missing}"\n\n#eval runPlanarPairingDependencyAudit\n'
with (p/'SourceGammaOneSmoothDivisorValueProbe907.lean').open('x',encoding='utf-8') as f:f.write(s)
print(json.dumps(dict(modules=len(mods),theorems=len(ths),definitions=len(defs),structures=structs)))
