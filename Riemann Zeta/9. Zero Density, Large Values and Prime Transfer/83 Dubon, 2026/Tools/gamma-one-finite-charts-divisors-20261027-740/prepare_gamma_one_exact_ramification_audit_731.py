from pathlib import Path
import json,re
p=Path(__file__).parent
mods=['SourceGammaOneExactRamification'];ns='Dubon2026.SourceFunctionField.GammaOne.'
ths=[ns+n for n in ['finrank_over_j_eq_index','sum_analytic_fiber_orders_eq_index','two_mul_ramification_eq_stabilizer_card']]
extra=[ns+n for n in ['sum_j_fiber_orders_eq_finrank','AnalyticFiberOrbits.exists_fiber_order_sum_eq_index','AnalyticFiberOrbits.sum_orders','AnalyticFiberOrbits.sum_relative_indices_eq_index','analytic_j_order_le_relative_index','analyticPlace_smul_plusMinus','OrbitCounting.relIndex_stabilizer_smul_of_mem']]
required=ths+extra;roots=ths;assert len(required)==10
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime
 assert not (Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')/f.name).exists()
closure=set(mods);todo=mods.copy()
while todo:
 for imp in re.findall(r'^import (\w+)$',(p/(todo.pop()+'.lean')).read_text(encoding='utf-8'),re.M):
  if (p/(imp+'.lean')).exists() and imp not in closure:closure.add(imp);todo.append(imp)
cfg=dict(modules=mods,theorems=ths,constructions=[],queries=ths,proofEdges=required,roots=roots,separatelyAxiomChecked=[],scratchImportClosure=sorted(closure),separateReason='Exact ramification at every actual Gamma1 analytic point follows from actual fixed-degree and generic fiber sums, termwise order bounds and actual place invariance. All nonzero levels are retained.')
def output(n,s):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(s)
output('source-gamma-one-exact-ramification-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneFourierConverseAudit2.lean').read_text(encoding='utf-8');body=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,values in [('modules',mods),('theorems',ths),('constructions',[])]:body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(values),body)
body=body.replace('SOURCE GAMMA ONE FOURIER CONVERSE','SOURCE GAMMA ONE EXACT RAMIFICATION').replace('Gamma One Fourier Converse','Gamma One Exact Ramification')
output('SourceGammaOneExactRamificationAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in ths)+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOneFourierConverseDependencyAudit2.lean').read_text(encoding='utf-8');body=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,values in [('roots',roots),('localModules',sorted(closure)),('required',required)]:body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(values),body)
body=body[:body.index('  logInfo m!')]+'  logInfo m!"SOURCE GAMMA ONE EXACT RAMIFICATION DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in exact ramification at every actual Gamma1 analytic place. Only declaration values are traversed. Fixed-degree and actual generic fiber sums identify the degree; equality of finite sums forces each termwise bound to be equality. All nonzero levels and elliptic points are covered. Ramified and cusp global charts, actual period and Hecke/diamond/Picard/H1 arithmetic comparison, all-weight characteristic-zero association and literal higher symmetric-power continuation remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOneExactRamificationDependencyAudit1.lean',imports+body)
route=json.loads((p/'gamma-one-exact-ramification-route-731.json').read_text(encoding='utf-8'))
output('gamma-one-exact-ramification-audit-route-731.json',json.dumps(route,indent=2)+'\n')
s=(p/'record_gamma_one_fourier_converse_702.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-fourier-converse-2','source-gamma-one-exact-ramification-1'),('SourceGammaOneFourierConverseAudit2','SourceGammaOneExactRamificationAudit1'),('SourceGammaOneFourierConverseDependencyAudit2','SourceGammaOneExactRamificationDependencyAudit1'),('SOURCE GAMMA ONE FOURIER CONVERSE','SOURCE GAMMA ONE EXACT RAMIFICATION'),('gamma-one-fourier-converse-audit-route-702.json','gamma-one-exact-ramification-audit-route-731.json'),('(2, 2, 10)','(1, 3, 10)'),(' == 2',' == 1'),('linterScopes=2','linterScopes=1'),('modules=2, queries=2','modules=1, queries=3'),('20261026','20261027'),('2026-10-26','2026-10-27')]:
 assert a in s,a;s=s.replace(a,b)
output('record_gamma_one_exact_ramification_731.py',s)
s=(p/'SourceGammaOneGenericFiberCountScratchOwnership729.lean').read_text(encoding='utf-8').replace('SourceGammaOneGenericFiberCount','SourceGammaOneExactRamification')
output('SourceGammaOneExactRamificationScratchOwnership731.lean',s)
print(json.dumps(dict(modules=1,queries=3,edges=10)))
