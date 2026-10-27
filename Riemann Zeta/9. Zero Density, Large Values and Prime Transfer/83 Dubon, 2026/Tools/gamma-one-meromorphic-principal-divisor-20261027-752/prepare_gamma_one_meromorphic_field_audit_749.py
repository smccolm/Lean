from pathlib import Path
import json,re,hashlib
p=Path(r'E:\Lean\.tmp\dubon83');ns='Dubon2026.SourceFunctionField.GammaOne.'
mods=['SourceGammaOnePoleClearedProduct','SourceGammaOnePoleClearedCuspBounds','SourceGammaOneMeromorphicFieldRealization']
ths=[ns+x for x in ['exists_pole_cleared_holomorphic_product','pole_bounds_of_local_product','meromorphic_cusps_of_holomorphic_pole_bounds','exists_original_field_of_prescribed_meromorphic_orders']]
required=ths+[ns+x for x in ['exists_original_pole_multiplier_at_analytic_places','holomorphic_realization_of_mem_all_analytic_places','exists_holomorphic_of_nonnegative_orders','holomorphic_invariant_of_local_eq','holomorphic_quotient_cusp_pole_bound','boundedAtImInfty_of_local_eq','exists_original_field_of_holomorphic','realize_mul_eventuallyEq','analyticPlace_order','analyticRamification_pos']]+['Dubon2026.SourceFricke.exists_cusp_represents_of_poleBounded'];assert len(required)==15
closure=mods+['SourceGammaOneOriginalPoleMultiplier','SourceGammaOnePoleClearedNormalization','SourceGammaOneUniformCuspPole','SourceGammaOneHolomorphicModularQuotient','SourceGammaOneHolomorphicFieldRealization','SourceGammaOneCuspBoundedRealization','SourceGammaOneCuspResidues']
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0;assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime
def output(n,t):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(t)
cfg=dict(modules=mods,theorems=ths,constructions=[],queries=ths,proofEdges=required,roots=ths,separatelyAxiomChecked=[],scratchImportClosure=closure,separateReason='Actual meromorphic field realization from the precise ramification-weighted finite-divisor orders and bounded translated cusps. Cusp-limit transfer and period existence remain.')
output('source-gamma-one-meromorphic-field-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneExactRamificationAudit1.lean').read_text(encoding='utf-8');b=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,v in [('modules',mods),('theorems',ths),('constructions',[])]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b.replace('SOURCE GAMMA ONE EXACT RAMIFICATION','SOURCE GAMMA ONE MEROMORPHIC FIELD').replace('Gamma One Exact Ramification','Gamma One Meromorphic Field')
output('SourceGammaOneMeromorphicFieldAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in ths)+'\n'+b+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOneExactRamificationDependencyAudit1.lean').read_text(encoding='utf-8');b=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,v in [('roots',ths),('localModules',closure),('required',required)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b[:b.index('  logInfo m!')]+'  logInfo m!"SOURCE GAMMA ONE MEROMORPHIC FIELD DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the actual original-field realization, with the pole multiplier, holomorphic product, cusp bounds and exact normalized analytic orders. Only declaration values are traversed. Nonzero cusp-limit transfer, global periods, Hecke/diamond/H1 arithmetic comparison, all-weight association and higher continuation remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOneMeromorphicFieldDependencyAudit1.lean',imports+b)
routes=[p/'gamma-one-pole-cleared-product-route-747.json',p/'gamma-one-pole-cleared-cusp-route-748.json',p/'gamma-one-meromorphic-field-assembly-route-749.json'];data=[json.loads(f.read_text()) for f in routes]
files=routes+[p/'source-gamma-one-holomorphic-field-1-scratch-receipt.json',p/'source-gamma-one-pole-clearing-normalization-1-scratch-receipt.json',p/'gamma-one-global-period-route-reuse-736/S_ModularCurve_ComplexPlaceDictionaryOf_exists_meromorphic_meromorphicOrderAt_eq_of_abelJacobi_mem_periodLatticeOf_gammaH.lean.txt']
rd=dict(chain=data[0]['chain'],assumptionsToDischarge=[d['assumptionsToDischarge'] for d in data],remaining=data[2]['remaining'],reuseChecked=[dict(path=str(f),sha256=hashlib.sha256(f.read_bytes()).hexdigest().upper()) for f in files],sourceContract=data[0]['sourceContract'])
output('gamma-one-meromorphic-field-audit-route-749.json',json.dumps(rd,indent=2)+'\n')
s=(p/'record_gamma_one_holomorphic_field_744.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-holomorphic-field-1','source-gamma-one-meromorphic-field-1'),('SourceGammaOneHolomorphicFieldAudit1','SourceGammaOneMeromorphicFieldAudit1'),('SourceGammaOneHolomorphicFieldDependencyAudit1','SourceGammaOneMeromorphicFieldDependencyAudit1'),('SOURCE GAMMA ONE HOLOMORPHIC FIELD','SOURCE GAMMA ONE MEROMORPHIC FIELD'),('gamma-one-holomorphic-field-audit-route-744.json','gamma-one-meromorphic-field-audit-route-749.json'),('(3, 5, 13)','(3, 4, 15)'),('modules=3, queries=5','modules=3, queries=4'),('all 13 required','all 15 required'),('requiredProofValueEdges=13','requiredProofValueEdges=15'),('proofEdges=13','proofEdges=15')]:
 assert a in s,a;s=s.replace(a,b)
output('record_gamma_one_meromorphic_field_749.py',s)
s=(p/'SourceGammaOneExactRamificationScratchOwnership731.lean').read_text(encoding='utf-8').replace('import SourceGammaOneExactRamification',''.join('import '+m+'\n' for m in mods).rstrip()).replace('#[`SourceGammaOneExactRamification]',arr(mods))
output('SourceGammaOneMeromorphicFieldScratchOwnership749.lean',s)
print(json.dumps(dict(modules=3,queries=4,edges=15)))
