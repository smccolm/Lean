from pathlib import Path
import json,re,hashlib
p=Path(__file__).parent
mods=['SourceGammaOneCuspBoundedRealization','SourceGammaOneCuspPlaceExhaustion'];ns='Dubon2026.SourceFunctionField.GammaOne.'
ths=[ns+n for n in ['holomorphic_quotient_cusp_eventuallyEq','holomorphic_quotient_bounded_of_cusp_regular','constant_of_mem_all_analytic_and_cusp_places','place_analytic_or_actual_cusp','exists_cusp_place_eq_of_j_pole','order_eq_zero_at_j_poles_of_cusp_limits']]
required=ths+['Dubon2026.SourceCurve.exists_nonconstant_regular_away_of_finite_coordinate','ModularForm.eq_const_of_weight_zero']+[ns+n for n in ['holomorphic_realization_of_mem_all_analytic_places','cuspPlace_order_eq_zero_of_tendsto','cuspRealize_tendsto_residue','quotient_cusp_represents','finiteDimensional_jCoordinateOver']]
assert len(required)==13
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime
closure=mods+['SourceGammaOneCuspResidues']
cfg=dict(modules=mods,theorems=ths,constructions=[],queries=ths,proofEdges=required,roots=ths,separatelyAxiomChecked=[],scratchImportClosure=closure,separateReason='Actual one-pole functions and native modular constancy exhaust every j-pole place by a genuine translated cusp. Nonzero limits then give order zero at every such place.')
def output(n,s):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(s)
output('source-gamma-one-cusp-exhaustion-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneExactRamificationAudit1.lean').read_text(encoding='utf-8');b=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,v in [('modules',mods),('theorems',ths),('constructions',[])]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b.replace('SOURCE GAMMA ONE EXACT RAMIFICATION','SOURCE GAMMA ONE CUSP EXHAUSTION').replace('Gamma One Exact Ramification','Gamma One Cusp Exhaustion')
output('SourceGammaOneCuspExhaustionAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in ths)+'\n'+b+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOneExactRamificationDependencyAudit1.lean').read_text(encoding='utf-8');b=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,v in [('roots',ths),('localModules',closure),('required',required)]:b=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(v),b)
b=b[:b.index('  logInfo m!')]+'  logInfo m!"SOURCE GAMMA ONE CUSP EXHAUSTION DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in actual cusp exhaustion and order zero at every j-pole place from nonzero cusp limits. Only declaration values are traversed. Native weight-zero constancy and the proved one-pole function are consumed. Global periods, Hecke/diamond/H1 arithmetic comparison, all-weight association and higher continuation remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOneCuspExhaustionDependencyAudit1.lean',imports+b)
rd=json.loads((p/'gamma-one-cusp-exhaustion-route-743.json').read_text());f=p/'source-gamma-one-cusp-residues-1-scratch-receipt.json';rd['reuseChecked'].append(dict(path=str(f),sha256=hashlib.sha256(f.read_bytes()).hexdigest().upper()))
output('gamma-one-cusp-exhaustion-audit-route-743.json',json.dumps(rd,indent=2)+'\n')
s=(p/'record_gamma_one_exact_ramification_731.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-exact-ramification-1','source-gamma-one-cusp-exhaustion-1'),('SourceGammaOneExactRamificationAudit1','SourceGammaOneCuspExhaustionAudit1'),('SourceGammaOneExactRamificationDependencyAudit1','SourceGammaOneCuspExhaustionDependencyAudit1'),('SOURCE GAMMA ONE EXACT RAMIFICATION','SOURCE GAMMA ONE CUSP EXHAUSTION'),('gamma-one-exact-ramification-audit-route-731.json','gamma-one-cusp-exhaustion-audit-route-743.json'),('(1, 3, 10)','(2, 6, 13)'),(' == 1',' == 2'),('linterScopes=1','linterScopes=2'),('modules=1, queries=3','modules=2, queries=6'),('all 10 required','all 13 required'),('requiredProofValueEdges=10','requiredProofValueEdges=13'),('proofEdges=10','proofEdges=13')]:
 assert a in s,a;s=s.replace(a,b)
output('record_gamma_one_cusp_exhaustion_743.py',s)
s=(p/'SourceGammaOneExactRamificationScratchOwnership731.lean').read_text(encoding='utf-8')
s=s.replace('import SourceGammaOneExactRamification',''.join('import '+m+'\n' for m in mods).rstrip()).replace('#[`SourceGammaOneExactRamification]',arr(mods))
output('SourceGammaOneCuspExhaustionScratchOwnership743.lean',s)
print(json.dumps(dict(modules=2,queries=6,edges=13)))
