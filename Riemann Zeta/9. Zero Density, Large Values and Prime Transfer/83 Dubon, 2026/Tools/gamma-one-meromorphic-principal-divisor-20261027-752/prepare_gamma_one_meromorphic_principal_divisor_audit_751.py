from pathlib import Path
import json,re,hashlib
p=Path(r'E:\Lean\.tmp\dubon83');ns='Dubon2026.SourceFunctionField.GammaOne.'
mods=['SourceGammaOneMeromorphicCuspLimits','SourceGammaOneMeromorphicPrincipalDivisor']
ths=[ns+x for x in ['tendsto_atImInfty_of_local_eq','eventually_continuousAt_realize_cusp','tendsto_cuspFunction_of_tendsto','cuspRealize_tendsto_of_local_eq','isPrincipal_of_prescribed_meromorphic_orders','analytic_divisor_isPrincipal_of_meromorphic_function']]
required=ths+[ns+x for x in ['exists_original_field_of_prescribed_meromorphic_orders','order_eq_zero_at_j_poles_of_cusp_limits','place_analytic_or_actual_cusp','cuspPlace_order_eq_zero_of_tendsto','eventually_ne_zero_translated_cuspFunction','realize_smul_eq_translated_ratio','exists_analytic_place_eq']]+['Function.Periodic.invQParam_tendsto','Dubon2026.SourceCurve.exists_nonconstant_regular_away_of_finite_coordinate'];assert len(required)==15
closure=mods+['SourceGammaOnePoleClearedProduct','SourceGammaOnePoleClearedCuspBounds','SourceGammaOneMeromorphicFieldRealization','SourceGammaOneOriginalPoleMultiplier','SourceGammaOnePoleClearedNormalization','SourceGammaOneUniformCuspPole','SourceGammaOneHolomorphicModularQuotient','SourceGammaOneHolomorphicFieldRealization','SourceGammaOneCuspBoundedRealization','SourceGammaOneCuspResidues','SourceGammaOneCuspPlaceExhaustion']
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0;assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime
def output(n,t):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(t)
cfg=dict(modules=mods,theorems=ths,constructions=[],queries=ths,proofEdges=required,roots=ths,separatelyAxiomChecked=[],scratchImportClosure=closure,separateReason='Exact meromorphic function contract gives a literal principal analytic divisor in the original Gamma1 field. Period-function existence is still required.')
output('source-gamma-one-meromorphic-principal-divisor-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneExactRamificationAudit1.lean').read_text(encoding='utf-8');b=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,v in [('modules',mods),('theorems',ths),('constructions',[])]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b.replace('SOURCE GAMMA ONE EXACT RAMIFICATION','SOURCE GAMMA ONE MEROMORPHIC PRINCIPAL DIVISOR').replace('Gamma One Exact Ramification','Gamma One Meromorphic Principal Divisor')
output('SourceGammaOneMeromorphicPrincipalDivisorAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in ths)+'\n'+b+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOneExactRamificationDependencyAudit1.lean').read_text(encoding='utf-8');b=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,v in [('roots',ths),('localModules',closure),('required',required)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b[:b.index('  logInfo m!')]+'  logInfo m!"SOURCE GAMMA ONE MEROMORPHIC PRINCIPAL DIVISOR DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the actual original-field principal divisor, including cusp-limit transfer, actual cusp exhaustion and every j-pole order. Only declaration values are traversed. Actual period-function existence, real period surjectivity, reciprocity, Hecke/diamond/H1 arithmetic comparison, all-weight association and higher continuation remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOneMeromorphicPrincipalDivisorDependencyAudit1.lean',imports+b)
routes=[p/'gamma-one-meromorphic-cusp-limits-route-750.json',p/'gamma-one-meromorphic-principal-divisor-route-751.json'];data=[json.loads(f.read_text()) for f in routes]
files=routes+[p/'source-gamma-one-meromorphic-field-1-scratch-receipt.json',p/'source-gamma-one-cusp-exhaustion-1-scratch-receipt.json']
rd=dict(chain=data[1]['chain'],assumptionsToDischarge=[d['assumptionsToDischarge'] for d in data],remaining=data[1]['remaining'],reuseChecked=data[0]['reuseChecked']+[dict(path=str(f),sha256=hashlib.sha256(f.read_bytes()).hexdigest().upper()) for f in files],shorterRoute=data[0]['shorterRoute'])
output('gamma-one-meromorphic-principal-divisor-audit-route-751.json',json.dumps(rd,indent=2)+'\n')
s=(p/'record_gamma_one_meromorphic_field_749.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-meromorphic-field-1','source-gamma-one-meromorphic-principal-divisor-1'),('SourceGammaOneMeromorphicFieldAudit1','SourceGammaOneMeromorphicPrincipalDivisorAudit1'),('SourceGammaOneMeromorphicFieldDependencyAudit1','SourceGammaOneMeromorphicPrincipalDivisorDependencyAudit1'),('SOURCE GAMMA ONE MEROMORPHIC FIELD','SOURCE GAMMA ONE MEROMORPHIC PRINCIPAL DIVISOR'),('gamma-one-meromorphic-field-audit-route-749.json','gamma-one-meromorphic-principal-divisor-audit-route-751.json'),('(3, 4, 15)','(2, 6, 15)'),(' == 3',' == 2'),('linterScopes=3','linterScopes=2'),('modules=3, queries=4','modules=2, queries=6')]:
 assert a in s,a;s=s.replace(a,b)
output('record_gamma_one_meromorphic_principal_divisor_751.py',s)
s=(p/'SourceGammaOneExactRamificationScratchOwnership731.lean').read_text(encoding='utf-8').replace('import SourceGammaOneExactRamification',''.join('import '+m+'\n' for m in mods).rstrip()).replace('#[`SourceGammaOneExactRamification]',arr(mods))
output('SourceGammaOneMeromorphicPrincipalDivisorScratchOwnership751.lean',s)
print(json.dumps(dict(modules=2,queries=6,edges=15)))
