from pathlib import Path
import json,re
p=Path(__file__).parent
mods=['SourceGammaOnePrescribedPlaceOrders','SourceGammaOneAnalyticDivisorMoving']
ns='Dubon2026.SourceFunctionField.GammaOne.'
ths=[ns+n for n in ['exists_polar_regular_separator','exists_prescribed_place_orders',
 'exists_divisor_analytic_decomposition','degree_mapDomain_analyticPlace','exists_degree_zero_analytic_representative']]
extra=['Dubon2026.SourceCurve.Place.exists_order_separating_function',
 'Dubon2026.SourceCurve.Place.exists_forall_ord_eq_of_sep',
 'Dubon2026.SourceCurve.finite_function_support_of_separating_coordinate',
 ns+'functionFieldOver_isCurveOver',ns+'exists_analytic_place_eq',ns+'place_residue_bijective']
required=ths+extra;roots=ths;assert len(required)==11
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime
 assert not (Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')/f.name).exists()
closure=set(mods);todo=mods.copy()
while todo:
 for imp in re.findall(r'^import (\w+)$',(p/(todo.pop()+'.lean')).read_text(encoding='utf-8'),re.M):
  if (p/(imp+'.lean')).exists() and imp not in closure:closure.add(imp);todo.append(imp)
cfg=dict(modules=mods,theorems=ths,constructions=[],queries=ths,proofEdges=required,roots=roots,
 separatelyAxiomChecked=[],scratchImportClosure=sorted(closure),
 separateReason='Actual principal-divisor subtraction and finite-place exhaustion realize every degree-zero divisor class by a finite analytic divisor of coefficient sum zero. Actual order prescription is proved, not assumed.')
def output(n,s):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(s)
output('source-gamma-one-divisor-moving-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneExactRamificationAudit1.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,values in [('modules',mods),('theorems',ths),('constructions',[])]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(values),body)
body=body.replace('SOURCE GAMMA ONE EXACT RAMIFICATION','SOURCE GAMMA ONE DIVISOR MOVING').replace('Gamma One Exact Ramification','Gamma One Divisor Moving')
output('SourceGammaOneDivisorMovingAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in ths)+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOneExactRamificationDependencyAudit1.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,values in [('roots',roots),('localModules',sorted(closure)),('required',required)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(values),body)
body=body[:body.index('  logInfo m!')]+'  logInfo m!"SOURCE GAMMA ONE DIVISOR MOVING DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in actual prescribed orders and analytic representatives of degree-zero divisor classes. Only declaration values are traversed. The actual principal-divisor and finite-exhaustion theorems are consumed; no approximation or moving certificate is supplied. Actual Picard/period and Hecke/diamond/H1 arithmetic comparison, all-weight association and literal higher symmetric-power continuation remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOneDivisorMovingDependencyAudit1.lean',imports+body)
route=json.loads((p/'gamma-one-divisor-moving-route-738.json').read_text(encoding='utf-8'))
output('gamma-one-divisor-moving-audit-route-738.json',json.dumps(route,indent=2)+'\n')
s=(p/'record_gamma_one_exact_ramification_731.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-exact-ramification-1','source-gamma-one-divisor-moving-1'),
 ('SourceGammaOneExactRamificationAudit1','SourceGammaOneDivisorMovingAudit1'),
 ('SourceGammaOneExactRamificationDependencyAudit1','SourceGammaOneDivisorMovingDependencyAudit1'),
 ('SOURCE GAMMA ONE EXACT RAMIFICATION','SOURCE GAMMA ONE DIVISOR MOVING'),
 ('gamma-one-exact-ramification-audit-route-731.json','gamma-one-divisor-moving-audit-route-738.json'),
 ('(1, 3, 10)','(2, 5, 11)'),(' == 1',' == 2'),('linterScopes=1','linterScopes=2'),
 ('modules=1, queries=3','modules=2, queries=5'),('all 10 required','all 11 required'),
 ('requiredProofValueEdges=10','requiredProofValueEdges=11'),('proofEdges=10','proofEdges=11')]:
 assert a in s,a;s=s.replace(a,b)
output('record_gamma_one_divisor_moving_738.py',s)
s=(p/'SourceGammaOneExactRamificationScratchOwnership731.lean').read_text(encoding='utf-8')
s=s.replace('import SourceGammaOneExactRamification',''.join('import '+m+'\n' for m in mods).rstrip())
s=s.replace('#[`SourceGammaOneExactRamification]',arr(mods))
assert 'SourceGammaOneExactRamification' not in s
output('SourceGammaOneDivisorMovingScratchOwnership738.lean',s)
print(json.dumps(dict(modules=2,queries=5,edges=11)))
