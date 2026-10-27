from pathlib import Path
import json,re
p=Path(__file__).parent
mods=['SourceGammaOneRamifiedMeromorphicOrder','SourceGammaOneNearbyOrders','SourceGammaOneRamifiedChartOrders']
ns='Dubon2026.SourceFunctionField.GammaOne.'
ths=[ns+n for n in ['meromorphicAt_ramifiedPlace_eval','ramifiedPlace_meromorphicOrderAt','ramifiedPlace_nearby_orders','analyticRamification_param_eventually_one','ramifiedPlace_chart_orders']]
cons=[];queries=ths+cons;roots=ths
required=queries+[ns+'ramifiedPlace_regular_analytic',ns+'ramifiedPlace_regular_order',ns+'place_eq_of_coord_power_eq','Dubon2026.SourceFunctionField.PowerDescent.exists_local_branch',ns+'analyticRamification_eventually_one','Dubon2026.SourceCurve.Place.rationalEval_inv',ns+'placeEval_meromorphicOrderAt']
assert len(required)==12
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime
 assert not (Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')/f.name).exists()
closure=set(mods);todo=mods.copy()
while todo:
 for imp in re.findall(r'^import (\w+)$',(p/(todo.pop()+'.lean')).read_text(encoding='utf-8'),re.M):
  if (p/(imp+'.lean')).exists() and imp not in closure:closure.add(imp);todo.append(imp)
cfg=dict(modules=mods,theorems=ths,constructions=cons,queries=queries,proofEdges=required,roots=roots,separatelyAxiomChecked=[],scratchImportClosure=sorted(closure),separateReason='Generic rational residue inversion extends the exact order to poles. The actual local analytic power branch and existing ramification isolation give one positive neighborhood with exact normalized orders for every nonzero function.')
def output(n,s):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(s)
output('source-gamma-one-ramified-chart-orders-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneFourierConverseAudit2.lean').read_text(encoding='utf-8');body=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,values in [('modules',mods),('theorems',ths),('constructions',cons)]:body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(values),body)
body=body.replace('SOURCE GAMMA ONE FOURIER CONVERSE','SOURCE GAMMA ONE RAMIFIED CHART ORDERS').replace('Gamma One Fourier Converse','Gamma One Ramified Chart Orders')
output('SourceGammaOneRamifiedChartOrdersAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in queries)+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOneFourierConverseDependencyAudit2.lean').read_text(encoding='utf-8');body=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,values in [('roots',roots),('localModules',sorted(closure)),('required',required)]:body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(values),body)
body=body[:body.index('  logInfo m!')]+'  logInfo m!"SOURCE GAMMA ONE RAMIFIED CHART ORDERS DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in actual Gamma1 common-neighborhood ramified chart orders. Only declaration values are traversed. Generic residue inversion extends the exact order to poles. Actual analytic power branches and isolated ramification give one radius for every nonzero function, including regular analyticity. All nonzero levels and elliptic points are covered. Uniformizer normalization, cusp/global charts, actual period and Hecke/diamond/Picard/H1 arithmetic comparison, all-weight characteristic-zero association and literal higher symmetric-power continuation remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOneRamifiedChartOrdersDependencyAudit1.lean',imports+body)
route=json.loads((p/'gamma-one-ramified-chart-orders-route-734.json').read_text(encoding='utf-8'))
output('gamma-one-ramified-chart-orders-audit-route-734.json',json.dumps(route,indent=2)+'\n')
s=(p/'record_gamma_one_fourier_converse_702.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-fourier-converse-2','source-gamma-one-ramified-chart-orders-1'),('SourceGammaOneFourierConverseAudit2','SourceGammaOneRamifiedChartOrdersAudit1'),('SourceGammaOneFourierConverseDependencyAudit2','SourceGammaOneRamifiedChartOrdersDependencyAudit1'),('SOURCE GAMMA ONE FOURIER CONVERSE','SOURCE GAMMA ONE RAMIFIED CHART ORDERS'),('gamma-one-fourier-converse-audit-route-702.json','gamma-one-ramified-chart-orders-audit-route-734.json'),('(2, 2, 10)','(3, 5, 12)'),(' == 2',' == 3'),('all 10 required proof dependencies','all 12 required proof dependencies'),('linterScopes=2','linterScopes=3'),('requiredProofValueEdges=10','requiredProofValueEdges=12'),('modules=2, queries=2','modules=3, queries=5'),('proofEdges=10','proofEdges=12'),('20261026','20261027'),('2026-10-26','2026-10-27')]:
 assert a in s,a;s=s.replace(a,b)
output('record_gamma_one_ramified_chart_orders_734.py',s)
s=(p/'SourceGammaOneGenericFiberCountScratchOwnership729.lean').read_text(encoding='utf-8')
s=s.replace('import SourceGammaOneGenericFiberCount',''.join('import '+m+'\n' for m in mods).rstrip())
s=s.replace('#[`SourceGammaOneGenericFiberCount]',arr(mods))
output('SourceGammaOneRamifiedChartOrdersScratchOwnership734.lean',s)
print(json.dumps(dict(modules=3,queries=5,edges=12)))
