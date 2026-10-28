from pathlib import Path
import json,re,ast,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
pairs=[('SourceSmoothComparisonQuotient','915a'),('SourceSmoothComparisonCusps','916a'),('SourceSmoothComparisonWindingLog','917a'),('SourceGammaOneDivisorWindingComparison','918b')]
mods=[m for m,e in pairs];ths=[];defs=[]
for m,e in pairs:
 f=p/(m+'.lean');t=f.read_text(encoding='utf-8')
 assert (p/(m+e+'.exit')).read_text().strip()=='0' and (p/(m+e+'.log')).stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 ns=re.search(r'^namespace (\S+)',t,re.M)[1]+'.'
 for kind,n in re.findall(r'^(theorem|def) (\S+)',t,re.M):(ths if kind=='theorem' else defs).append(ns+n)
queries=ths+defs
required=queries+[
'Dubon2026.SourceFunctionField.GammaOne.exists_original_divisor_smooth_period_limit',
'Dubon2026.sourceGamma1_meromorphic_multiplier_eq_exp_real_period',
'Dubon2026.SourcePeriodUntwist.Φ_local','Dubon2026.SourcePeriodUntwist.Φ_smul',
'Dubon2026.SourcePeriodUntwist.Φ_cusp','Dubon2026.SourcePeriodUntwist.Φ_decay',
'Dubon2026.SourceSmoothLocalModel.regularize_eventuallyEq',
'Dubon2026.SourceSmoothDivisor.Data.tendsto_sm_nhdsNE',
'Dubon2026.SourceWindingLog.exists_parabolic_log',
'Dubon2026.SourceSmoothedFundamental.im_smul_le_max','Filter.Tendsto.limUnder_eq']
closure=list(mods)
for name in ['source-gamma-one-smooth-divisor-period-1b','source-gamma-one-invariant-untwist-1','source-modular-parabolic-winding-log-1']:
 c=json.loads((p/(name+'-audit-config.json')).read_text(encoding='utf-8'))
 closure+=c.get('scratchImportClosure',c['modules'])
closure=list(dict.fromkeys(closure))
roots=['Dubon2026.SourceFunctionField.GammaOne.exists_original_divisor_winding_comparison']
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=queries,compileEvidence={m:m+e for m,e in pairs},proofEdges=required,roots=roots,scratchImportClosure=closure,separatelyAxiomChecked=[],separateReason='Every retained declaration is consumed by the actual original-divisor winding comparison, including the equality with the source punctured-limit convention.')
def out(n,t):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(t)
out('source-gamma-one-divisor-winding-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda ns:'#['+', '.join(chr(96)+n for n in ns)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneSmoothDivisorPeriodAudit1.lean').read_text(encoding='utf-8')
b=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k in ['modules','theorems','constructions']:
 b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(cfg[k]),b)
b=b.replace('SOURCE GAMMA ONE SMOOTH DIVISOR PERIOD','SOURCE GAMMA ONE DIVISOR WINDING').replace('Gamma One Smooth Divisor Period','Gamma One Divisor Winding')
out('SourceGammaOneDivisorWindingAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in queries)+'\n'+b+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOneSmoothDivisorPeriodDependencyAudit1b.lean').read_text(encoding='utf-8')
b=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,v in [('roots',roots),('localModules',closure),('required',required)]:
 b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b[:b.index('  logInfo m!')]+'  logInfo m!"SOURCE GAMMA ONE DIVISOR WINDING DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the declaration-VALUE closure of the actual original-divisor winding consumer. The original multiplier produces the cusp form; the degree-zero divisor produces V and its original period limit. Local cancellation, removable filling and actual cusp transfer produce the nonvanishing invariant quotient and its parabolic integer logarithmic character. Source punctured-limit normalization is preserved. Winding side pairing, analytic reciprocity and the full all-weight goal remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
out('SourceGammaOneDivisorWindingDependencyAudit1.lean',imports+b)
t=(p/'SourceGammaOneSmoothDivisorPeriodScratchOwnership914.lean').read_text(encoding='utf-8')
b=t[t.index('private def inspectOwnership'):]
b=re.sub(r'let mods : Array Name := #\[[^\n]*',lambda _:'let mods : Array Name := '+arr(mods),b)
out('SourceGammaOneDivisorWindingScratchOwnership919.lean',imports+b)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
paths=[p/'gamma-one-divisor-winding-comparison-route-918.json',p/'smooth-comparison-quotient-route-915.json',p/'source-gamma-one-smooth-divisor-period-1b-scratch-receipt.json',p/'source-modular-parabolic-winding-log-1-scratch-receipt.json']
route=json.loads(paths[0].read_text(encoding='utf-8'))
route['reuseChecked']=[dict(path=str(f),sha256=sha(f)) for f in paths]
out('source-gamma-one-divisor-winding-audit-route-919.json',json.dumps(route,indent=2)+'\n')
t=(p/'record_source_gamma_one_smooth_divisor_period_914b.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-smooth-divisor-period-1b','source-gamma-one-divisor-winding-1'),('SourceGammaOneSmoothDivisorPeriodAudit1','SourceGammaOneDivisorWindingAudit1'),('SourceGammaOneSmoothDivisorPeriodDependencyAudit1b','SourceGammaOneDivisorWindingDependencyAudit1'),('SOURCE GAMMA ONE SMOOTH DIVISOR PERIOD','SOURCE GAMMA ONE DIVISOR WINDING'),('source-gamma-one-smooth-divisor-period-audit-route-914.json','source-gamma-one-divisor-winding-audit-route-919.json'),('(5, 18, 29)',str((len(mods),len(queries),len(required)))),('all 29 required',f'all {len(required)} required'),('requiredProofValueEdges=29',f'requiredProofValueEdges={len(required)}'),('modules=5, queries=18',f'modules={len(mods)}, queries={len(queries)}'),('proofEdges=29',f'proofEdges={len(required)}'),('== 5',f'== {len(mods)}'),('linterScopes=5',f'linterScopes={len(mods)}')]:
 assert a in t,a
 t=t.replace(a,b)
ast.parse(t);out('record_source_gamma_one_divisor_winding_919.py',t)
t=(p/'audit_smooth_divisor_period_914.ps1').read_text(encoding='utf-8')
for a,b in [('SourceGammaOneSmoothDivisorPeriodAudit1','SourceGammaOneDivisorWindingAudit1'),('SourceGammaOneSmoothDivisorPeriodDependencyAudit1','SourceGammaOneDivisorWindingDependencyAudit1'),('SourceGammaOneSmoothDivisorPeriodScratchOwnership914','SourceGammaOneDivisorWindingScratchOwnership919'),('record_source_gamma_one_smooth_divisor_period_914.py','record_source_gamma_one_divisor_winding_919.py')]:t=t.replace(a,b)
out('audit_divisor_winding_919.ps1',t)
print(json.dumps(dict(modules=len(mods),theorems=len(ths),constructions=len(defs),queries=len(queries),required=len(required))))
