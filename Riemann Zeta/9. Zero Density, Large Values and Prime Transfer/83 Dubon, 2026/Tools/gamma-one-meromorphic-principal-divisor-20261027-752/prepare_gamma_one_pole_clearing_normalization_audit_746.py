from pathlib import Path
import json,re,hashlib
p=Path(r'E:\Lean\.tmp\dubon83');ns='Dubon2026.SourceFunctionField.GammaOne.'
mods=['SourceGammaOneOriginalPoleMultiplier','SourceGammaOnePoleClearedNormalization']
ths=[ns+x for x in ['exists_original_pole_multiplier','exists_original_pole_multiplier_at_analytic_places','exists_holomorphic_of_nonnegative_orders','holomorphic_invariant_of_local_eq','boundedAtImInfty_of_local_eq']]
required=ths+['Dubon2026.SourceCurve.exists_pole_clearing_function_of_finite_coordinate']+[ns+x for x in ['finiteDimensional_jCoordinateOver','cuspPlace_j_neg','analyticPlace_j_sub_pos']]+['meromorphicNFOn_toMeromorphicNFOn','meromorphicOrderAt_toMeromorphicNFOn','Homeomorph.map_punctured_nhds_eq','UpperHalfPlane.isBoundedAtImInfty_iff'];assert len(required)==13
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0;assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime
def output(n,t):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(t)
cfg=dict(modules=mods,theorems=ths,constructions=[],queries=ths,proofEdges=required,roots=ths,separatelyAxiomChecked=[],scratchImportClosure=mods,separateReason='Actual algebraic pole multiplier and native analytic normalization, with invariance and cusp boundedness preserved. The consumer forming the actual meromorphic product remains separate.')
output('source-gamma-one-pole-clearing-normalization-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneExactRamificationAudit1.lean').read_text(encoding='utf-8');b=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,v in [('modules',mods),('theorems',ths),('constructions',[])]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b.replace('SOURCE GAMMA ONE EXACT RAMIFICATION','SOURCE GAMMA ONE POLE CLEARING NORMALIZATION').replace('Gamma One Exact Ramification','Gamma One Pole Clearing Normalization')
output('SourceGammaOnePoleClearingNormalizationAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in ths)+'\n'+b+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOneExactRamificationDependencyAudit1.lean').read_text(encoding='utf-8');b=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,v in [('roots',ths),('localModules',mods),('required',required)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b[:b.index('  logInfo m!')]+'  logInfo m!"SOURCE GAMMA ONE POLE CLEARING NORMALIZATION DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the original algebraic pole multiplier and native holomorphic normalization, subgroup invariance and cusp bound preservation. Only declaration values are traversed. Actual product assembly, global periods, Hecke/diamond/H1 arithmetic comparison, all-weight association and higher continuation remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOnePoleClearingNormalizationDependencyAudit1.lean',imports+b)
routes=[p/'gamma-one-original-pole-multiplier-route-745.json',p/'gamma-one-pole-cleared-normalization-route-746.json'];data=[json.loads(f.read_text()) for f in routes]
rd=dict(chain=data[0]['chain'],assumptionsToDischarge=[d['assumptionsToDischarge'] for d in data],remaining=data[1]['remaining'],reuseChecked=[x for d in data for x in d['reuseChecked']]+[dict(path=str(f),sha256=hashlib.sha256(f.read_bytes()).hexdigest().upper()) for f in routes],shorterRoutes=[d['shorterRoute'] for d in data])
output('gamma-one-pole-clearing-normalization-audit-route-746.json',json.dumps(rd,indent=2)+'\n')
s=(p/'record_gamma_one_holomorphic_field_744.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-holomorphic-field-1','source-gamma-one-pole-clearing-normalization-1'),('SourceGammaOneHolomorphicFieldAudit1','SourceGammaOnePoleClearingNormalizationAudit1'),('SourceGammaOneHolomorphicFieldDependencyAudit1','SourceGammaOnePoleClearingNormalizationDependencyAudit1'),('SOURCE GAMMA ONE HOLOMORPHIC FIELD','SOURCE GAMMA ONE POLE CLEARING NORMALIZATION'),('gamma-one-holomorphic-field-audit-route-744.json','gamma-one-pole-clearing-normalization-audit-route-746.json'),('(3, 5, 13)','(2, 5, 13)'),(' == 3',' == 2'),('linterScopes=3','linterScopes=2'),('modules=3, queries=5','modules=2, queries=5')]:
 assert a in s,a;s=s.replace(a,b)
output('record_gamma_one_pole_clearing_normalization_746.py',s)
s=(p/'SourceGammaOneExactRamificationScratchOwnership731.lean').read_text(encoding='utf-8').replace('import SourceGammaOneExactRamification',''.join('import '+m+'\n' for m in mods).rstrip()).replace('#[`SourceGammaOneExactRamification]',arr(mods))
output('SourceGammaOnePoleClearingNormalizationScratchOwnership746.lean',s)
print(json.dumps(dict(modules=2,queries=5,edges=13)))
