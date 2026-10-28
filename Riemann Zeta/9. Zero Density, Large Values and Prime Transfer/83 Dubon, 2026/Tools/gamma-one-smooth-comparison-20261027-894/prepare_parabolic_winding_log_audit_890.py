from pathlib import Path
import json,re,ast,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
mods=['SourceComplexWindingLogLift','SourceModularWindingCharacter','SourceModularWindingCuspLimit','SourceModularParabolicWindingLog']
ths=[];defs=[]
for m in mods:
 t=(p/(m+'.lean')).read_text(encoding='utf-8')
 ns=re.search(r'^namespace (\S+)',t,re.M)[1]+'.'
 for kind,n in re.findall(r'^(?:noncomputable )?(theorem|def) (\S+)',t,re.M):
  (ths if kind=='theorem' else defs).append(ns+n)
queries=ths+defs
required=queries+['Complex.isCoveringMap_exp','IsCoveringMap.const_of_comp','IsCoveringMap.existsUnique_continuousMap_lifts','Dubon2026.SourceParabolic.classification']
roots=['Dubon2026.SourceWindingLog.exists_parabolic_log']
ev=dict(zip(mods,[m+s for m,s in zip(mods,['887a','887a','887a','888b'])]))
for m in mods:
 f=p/(m+'.lean')
 assert (p/(ev[m]+'.exit')).read_text().strip()=='0' and (p/(ev[m]+'.log')).stat().st_size==0
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime
def output(n,t):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(t)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=queries,compileEvidence=ev,proofEdges=required,roots=roots,scratchImportClosure=mods,separatelyAxiomChecked=[],separateReason='All new declarations consumed by the actual logarithm construction. Instantiation at the filled actual comparison quotient is a later obligation.')
output('source-modular-parabolic-winding-log-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOnePeterssonSmoothLimitAudit1.lean').read_text(encoding='utf-8-sig')
b=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b.replace('SOURCE GAMMA ONE PETERSSON SMOOTH LIMIT','SOURCE MODULAR PARABOLIC WINDING LOG').replace('Gamma One Petersson Smooth Limit','Modular Parabolic Winding Log')
output('SourceModularParabolicWindingLogAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in queries)+'\n'+b+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOnePeterssonSmoothLimitDependencyAudit1.lean').read_text(encoding='utf-8-sig')
b=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,v in [('roots',roots),('localModules',mods),('required',required)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b[:b.index('  logInfo m!')]+'  logInfo m!"SOURCE MODULAR PARABOLIC WINDING LOG DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the declaration-VALUE closure of the constructed logarithm and literal squared-trace-four integral character. Native exponential covering, lift uniqueness and existing signed-translation classification are consumed. Actual comparison quotient construction and analytic reciprocity remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceModularParabolicWindingLogDependencyAudit1.lean',imports+b)
t=(p/'SourceGammaOnePeterssonSmoothLimitScratchOwnership885.lean').read_text(encoding='utf-8-sig')
b=t[t.index('private def inspectOwnership'):]
b=re.sub(r'let mods : Array Name := #\[[^\n]*',lambda _:'let mods : Array Name := '+arr(mods),b)
output('SourceModularParabolicWindingLogScratchOwnership890.lean',imports+b)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
r=Path(r'E:\Lean\Riemann Zeta')
paths=[p/'winding-log-reuse-route-887.json',p/'anthropic-flt-residual-closure-20261020/P2M/Sol/S_ModularCurve_exists_exp_eq_of_invariant_ne_zero_isParabolicHom.lean.txt',r/'.lake/packages/mathlib/Mathlib/Topology/Covering/Basic.lean',r/'.lake/packages/mathlib/Mathlib/Topology/Homotopy/Lifting.lean',r/'.lake/packages/mathlib/Mathlib/Analysis/Complex/CoveringMap.lean',r/'9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026/Extension/Dubon2026/SourceParabolicClassification.lean',r/'9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026/Extension/Dubon2026/SourceGammaOneRealParabolicPeriods.lean']
route=dict(chain=json.loads(paths[0].read_text(encoding='utf-8'))['chain'],reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in paths],assumptionsToDischarge=['Construct global continuous logarithm by native exponential covering and prove local C1 regularity and logarithmic derivative','Derive actual integer additive character from exponential invariance; native covering uniqueness supplies constancy','Prove finite translated logarithm cusp limits from nonzero finite function limits','Existing signed-translation classification and cusp limits prove literal squared-trace-four character vanishing'],remaining='Input is an actual C1 nonzero invariant function with nonzero translated cusp limits. The smooth comparison local model, filled quotient, winding-period integral, analytic reciprocity, original principal-divisor converse and full all-weight arithmetic chain remain. 16/20; DUB-17--20 OPEN.')
output('source-modular-parabolic-winding-log-audit-route-890.json',json.dumps(route,indent=2)+'\n')
t=(p/'record_source_gamma_one_petersson_smooth_limit_885.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-petersson-smooth-limit-1','source-modular-parabolic-winding-log-1'),('SourceGammaOnePeterssonSmoothLimit','SourceModularParabolicWindingLog'),('SOURCE GAMMA ONE PETERSSON SMOOTH LIMIT','SOURCE MODULAR PARABOLIC WINDING LOG'),('source-gamma-one-petersson-smooth-limit-audit-route-885.json','source-modular-parabolic-winding-log-audit-route-890.json'),('(6, 26, 41)',str((len(mods),len(queries),len(required)))),('all 41 required',f'all {len(required)} required'),('requiredProofValueEdges=41',f'requiredProofValueEdges={len(required)}'),('modules=6, queries=26',f'modules={len(mods)}, queries={len(queries)}'),('proofEdges=41',f'proofEdges={len(required)}'),('== 6',f'== {len(mods)}'),('linterScopes=6',f'linterScopes={len(mods)}')]:
 assert a in t,a
 t=t.replace(a,b)
ast.parse(t);output('record_source_modular_parabolic_winding_log_890.py',t)
print(json.dumps(dict(modules=len(mods),theorems=len(ths),constructions=len(defs),queries=len(queries),required=len(required))))
