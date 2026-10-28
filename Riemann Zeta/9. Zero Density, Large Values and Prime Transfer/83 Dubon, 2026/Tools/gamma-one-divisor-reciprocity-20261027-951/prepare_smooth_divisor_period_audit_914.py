from pathlib import Path
import json,re,ast,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
pairs=[('SourceSmoothOrbitIntegralGeometry','910b'),('SourceSmoothOrbitIntegralChangeVariables','910c'),('SourceSmoothCompactTranslateIntegral','911b'),('SourceSmoothDivisorPeriodIntegral','912b'),('SourceGammaOneSmoothDivisorPeriodIntegral','913a')]
mods=[m for m,e in pairs];ths=[]
for m,e in pairs:
 f=p/(m+'.lean');t=f.read_text(encoding='utf-8')
 assert (p/(m+e+'.exit')).read_text().strip()=='0' and (p/(m+e+'.log')).stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 ns=re.search(r'^namespace (\S+)',t,re.M)[1]+'.'
 ths+=[ns+n for n in re.findall(r'^theorem (\S+)',t,re.M)]
required=ths+[
'Dubon2026.SourceSmoothDivisor.exists_invariant_comparison',
'Dubon2026.SourceFunctionField.GammaOne.analyticRamification_smul_signed',
'Dubon2026.SourceFunctionField.GammaOne.exists_degree_zero_reciprocity_data',
'Dubon2026.SourceFunctionField.GammaOne.weighted_analytic_order_eq_half_coefficient',
'Dubon2026.SourceFunctionField.GammaOne.SignedForms.along_extend',
'Dubon2026.SourcePeriodUntwist.Ek_hasDerivAt',
'Dubon2026.SourceSmoothedFundamental.smooth_partition',
'Dubon2026.SourceSmoothDivisor.finite_moving\'',
'Dubon2026.SourceComplexReciprocity.continuous_mul_of_tsupport_subset',
'integral_image_eq_integral_abs_det_fderiv_smul','IsCompact.bddAbove_image']
roots=['Dubon2026.SourceFunctionField.GammaOne.exists_original_divisor_smooth_period_limit']
prior=json.loads((p/'source-gamma-one-smooth-divisor-1b-audit-config.json').read_text(encoding='utf-8'))
closure=list(dict.fromkeys(mods+prior['scratchImportClosure']))
cfg=dict(modules=mods,theorems=ths,constructions=[],queries=ths,compileEvidence={m:m+e for m,e in pairs},proofEdges=required,roots=roots,scratchImportClosure=closure,separatelyAxiomChecked=[],separateReason='All retained declarations serve the actual original Gamma1 divisor period-limit consumer. Native compact boundedness replaces a dominated-convergence layer.')
def out(n,t):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(t)
out('source-gamma-one-smooth-divisor-period-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda ns:'#['+', '.join(chr(96)+n for n in ns)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneSmoothDivisorAudit1b.lean').read_text(encoding='utf-8')
b=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k in ['modules','theorems','constructions']:
 b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(cfg[k]),b)
b=b.replace('SOURCE GAMMA ONE SMOOTH DIVISOR','SOURCE GAMMA ONE SMOOTH DIVISOR PERIOD').replace('Gamma One Smooth Divisor','Gamma One Smooth Divisor Period')
out('SourceGammaOneSmoothDivisorPeriodAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in ths)+'\n'+b+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOneSmoothDivisorDependencyAudit1b.lean').read_text(encoding='utf-8')
b=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,v in [('roots',roots),('localModules',closure),('required',required)]:
 b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b[:b.index('  logInfo m!')]+'  logInfo m!"SOURCE GAMMA ONE SMOOTH DIVISOR PERIOD DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the declaration-VALUE closure of the actual original Gamma1 divisor period-limit consumer. The constructed V, original degree-zero divisor, exact ramification, original cusp-form functions and endpoint periods are consumed. Native compact boundedness gives eventual exact unfolding. Filled quotient, winding reciprocity and full all-weight chain remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
out('SourceGammaOneSmoothDivisorPeriodDependencyAudit1.lean',imports+b)
t=(p/'SourceGammaOneSmoothDivisorScratchOwnership909b.lean').read_text(encoding='utf-8')
b=t[t.index('private def inspectOwnership'):]
b=re.sub(r'let mods : Array Name := #\[[^\n]*',lambda _:'let mods : Array Name := '+arr(mods),b)
out('SourceGammaOneSmoothDivisorPeriodScratchOwnership914.lean',imports+b)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
paths=[p/'smooth-orbit-integral-shorter-route-910.json',p/'smooth-divisor-period-route-912.json',p/'source-gamma-one-smooth-divisor-1b-scratch-receipt.json',p/'SourceWeightTwoPeriodUntwist.lean']
route=dict(chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> full all-weight arithmetic association -> original Gamma1 Picard/H1 -> Abel-Jacobi converse -> analytic reciprocity -> original smooth divisor period term',reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in paths],shorterRoute='Finite compact overlap plus native change of variables gives exact unfolding. Native compact boundedness and the existing exact partition formula give eventual exact equality, eliminating dominated-convergence bookkeeping. Reuse the normalized endpoint primitive and exact stabilizer/ramification formula; preserve original Gamma1 forms and periods under signed extension.',assumptionsToDischarge=['Integrability of the constructed comparison logarithmic derivative against the canonical smooth cutoff','Its exact normalized limit with actual original-divisor coefficients and original Gamma1 endpoint periods','Derive all compact coefficient, degree-zero, order-divisibility and primitive inputs from proved upstream constructions'],remaining='The filled quotient, winding-period and Petersson assembly must still establish analytic reciprocity and the original principal-divisor converse. The full all-weight arithmetic realization, automorphy and higher symmetric-power continuation chain remains. 16/20; DUB-17--20 OPEN.')
out('source-gamma-one-smooth-divisor-period-audit-route-914.json',json.dumps(route,indent=2)+'\n')
t=(p/'record_source_gamma_one_smooth_divisor_909b.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-smooth-divisor-1b','source-gamma-one-smooth-divisor-period-1'),('SourceGammaOneSmoothDivisorAudit1b','SourceGammaOneSmoothDivisorPeriodAudit1'),('SourceGammaOneSmoothDivisorDependencyAudit1b','SourceGammaOneSmoothDivisorPeriodDependencyAudit1'),('SOURCE GAMMA ONE SMOOTH DIVISOR','SOURCE GAMMA ONE SMOOTH DIVISOR PERIOD'),('source-gamma-one-smooth-divisor-audit-route-909.json','source-gamma-one-smooth-divisor-period-audit-route-914.json'),('(14, 90, 102)',str((len(mods),len(ths),len(required)))),('all 102 required',f'all {len(required)} required'),('requiredProofValueEdges=102',f'requiredProofValueEdges={len(required)}'),('modules=14, queries=90',f'modules={len(mods)}, queries={len(ths)}'),('proofEdges=102',f'proofEdges={len(required)}'),('== 14',f'== {len(mods)}'),('linterScopes=14',f'linterScopes={len(mods)}')]:
 assert a in t,a
 t=t.replace(a,b)
ast.parse(t);out('record_source_gamma_one_smooth_divisor_period_914.py',t)
t=(p/'audit_smooth_divisor_909b.ps1').read_text(encoding='utf-8')
for a,b in [('SourceGammaOneSmoothDivisorAudit1b','SourceGammaOneSmoothDivisorPeriodAudit1'),('SourceGammaOneSmoothDivisorDependencyAudit1b','SourceGammaOneSmoothDivisorPeriodDependencyAudit1'),('SourceGammaOneSmoothDivisorScratchOwnership909b','SourceGammaOneSmoothDivisorPeriodScratchOwnership914'),('record_source_gamma_one_smooth_divisor_909b.py','record_source_gamma_one_smooth_divisor_period_914.py')]:t=t.replace(a,b)
out('audit_smooth_divisor_period_914.ps1',t)
print(json.dumps(dict(modules=len(mods),queries=len(ths),required=len(required))))
