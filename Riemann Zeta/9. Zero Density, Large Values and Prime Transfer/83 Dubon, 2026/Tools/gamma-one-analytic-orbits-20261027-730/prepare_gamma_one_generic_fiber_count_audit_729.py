from pathlib import Path
import json,re
p=Path(__file__).parent
mods=['SourceGammaOneGenericFiberCount'];ns='Dubon2026.SourceFunctionField.GammaOne.AnalyticFiberOrbits.'
ths=[ns+n for n in ['sum_relative_indices_eq_index','exists_fiber_order_sum_eq_index']]
extra=['Dubon2026.SourceFunctionField.JMultiplicity.jf_surjective','Dubon2026.SourceFunctionField.JMultiplicity.case_generic','Dubon2026.SourceFunctionField.GammaOne.analytic_j_order_le_relative_index','Dubon2026.SourceFunctionField.GammaOne.two_le_card_stabilizer_plusMinus',ns+'sum_orders','Dubon2026.SourceFunctionField.GammaOne.OrbitCounting.finsum_relIndex_stabilizer_eq_index']
required=ths+extra;roots=ths;assert len(required)==8
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime
 assert not (Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')/f.name).exists()
closure=set(mods);todo=mods.copy()
while todo:
 for imp in re.findall(r'^import (\w+)$',(p/(todo.pop()+'.lean')).read_text(encoding='utf-8'),re.M):
  if (p/(imp+'.lean')).exists() and imp not in closure:closure.add(imp);todo.append(imp)
cfg=dict(modules=mods,theorems=ths,constructions=[],queries=ths,proofEdges=required,roots=roots,separatelyAxiomChecked=[],scratchImportClosure=sorted(closure),separateReason='A genuine generic j fiber has total positive order equal to the subgroup index, using actual j-surjectivity, exact orbit-fiber comparison and the termwise ramification bound.')
def output(n,s):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(s)
output('source-gamma-one-generic-fiber-count-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneFourierConverseAudit2.lean').read_text(encoding='utf-8');body=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,values in [('modules',mods),('theorems',ths),('constructions',[])]:body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(values),body)
body=body.replace('SOURCE GAMMA ONE FOURIER CONVERSE','SOURCE GAMMA ONE GENERIC FIBER COUNT').replace('Gamma One Fourier Converse','Gamma One Generic Fiber Count')
output('SourceGammaOneGenericFiberCountAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in ths)+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOneFourierConverseDependencyAudit2.lean').read_text(encoding='utf-8');body=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,values in [('roots',roots),('localModules',sorted(closure)),('required',required)]:body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(values),body)
body=body[:body.index('  logInfo m!')]+'  logInfo m!"SOURCE GAMMA ONE GENERIC FIBER COUNT DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in an actual generic finite j fiber with total order equal to the subgroup index. Only declaration values are traversed. Existing j-surjectivity constructs the point; actual finite-fiber bijection, native orbit counting and the termwise bound determine the multiplicities. Compose the fixed-degree fiber formula to obtain exact elliptic ramification; global charts remain. Original chart/period, Hecke/diamond/Picard/H1 arithmetic comparison, all-weight characteristic-zero association and literal higher symmetric-power continuation remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOneGenericFiberCountDependencyAudit1.lean',imports+body)
route=json.loads((p/'gamma-one-generic-fiber-count-route-729b.json').read_text(encoding='utf-8'))
output('gamma-one-generic-fiber-count-audit-route-729.json',json.dumps(route,indent=2)+'\n')
s=(p/'record_gamma_one_fourier_converse_702.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-fourier-converse-2','source-gamma-one-generic-fiber-count-1'),('SourceGammaOneFourierConverseAudit2','SourceGammaOneGenericFiberCountAudit1'),('SourceGammaOneFourierConverseDependencyAudit2','SourceGammaOneGenericFiberCountDependencyAudit1'),('SOURCE GAMMA ONE FOURIER CONVERSE','SOURCE GAMMA ONE GENERIC FIBER COUNT'),('gamma-one-fourier-converse-audit-route-702.json','gamma-one-generic-fiber-count-audit-route-729.json'),('(2, 2, 10)','(1, 2, 8)'),(' == 2',' == 1'),('all 10 required proof dependencies','all 8 required proof dependencies'),('linterScopes=2','linterScopes=1'),('requiredProofValueEdges=10','requiredProofValueEdges=8'),('modules=2, queries=2','modules=1, queries=2'),('proofEdges=10','proofEdges=8')]:
 assert a in s,a;s=s.replace(a,b)
output('record_gamma_one_generic_fiber_count_729.py',s)
print(json.dumps(dict(modules=1,queries=2,edges=8)))