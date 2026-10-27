from pathlib import Path
import json,re
p=Path(__file__).parent
mods=['SourceGammaOneRamificationBounds'];ns='Dubon2026.SourceFunctionField.GammaOne.'
ths=[ns+n for n in ['analytic_j_multiplicity', 'analytic_j_order_le_relative_index']]
cons=[ns+n for n in []]
extra=[ns+'plusMinus_stabilizer_card_dvd_two_mul_ramification',ns+'OrbitCounting.relIndex_stabilizer_mul_card_stabilizer','Dubon2026.SourceFunctionField.StabilizerCharacter.two_dvd_card_stabilizer',ns+'analyticPlace_order',ns+'analyticOrder_j_sub']
required=ths+extra;roots=ths+cons;assert len(required)==7
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime
 assert not (Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')/f.name).exists()
closure=set(mods);todo=mods.copy()
while todo:
 for imp in re.findall(r'^import (\w+)$',(p/(todo.pop()+'.lean')).read_text(encoding='utf-8'),re.M):
  if (p/(imp+'.lean')).exists() and imp not in closure:closure.add(imp);todo.append(imp)
cfg=dict(modules=mods,theorems=ths,constructions=cons,queries=ths+cons,proofEdges=required,roots=roots,separatelyAxiomChecked=[],scratchImportClosure=sorted(closure),separateReason='actual finite j-fiber orders bounded by subgroup relative stabilizer indices, with equality implying the exact ramification formula.')
def output(n,s):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(s)
output('source-gamma-one-ramification-bounds-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneFourierConverseAudit2.lean').read_text(encoding='utf-8');body=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,values in [('modules',mods),('theorems',ths),('constructions',cons)]:body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(values),body)
body=body.replace('SOURCE GAMMA ONE FOURIER CONVERSE','SOURCE GAMMA ONE RAMIFICATION BOUNDS').replace('Gamma One Fourier Converse','Gamma One Ramification Bounds')
output('SourceGammaOneRamificationBoundsAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in ths+cons)+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOneFourierConverseDependencyAudit2.lean').read_text(encoding='utf-8');body=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,values in [('roots',roots),('localModules',sorted(closure)),('required',required)]:body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(values),body)
body=body[:body.index('  logInfo m!')]+'  logInfo m!"SOURCE GAMMA ONE RAMIFICATION BOUNDS DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in actual finite j-fiber orders bounded by subgroup relative stabilizer indices, with equality implying the exact ramification formula. Only declaration values are traversed. The weighted finite-fiber comparison must still establish exact elliptic ramification; global charts remain. Original chart/period, Hecke/diamond/Picard/H1 arithmetic comparison, all-weight characteristic-zero association and literal higher symmetric-power continuation remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOneRamificationBoundsDependencyAudit1.lean',imports+body)
route=json.loads((p/'gamma-one-ramification-bounds-route-727b.json').read_text(encoding='utf-8'))
output('gamma-one-ramification-bounds-audit-route-727.json',json.dumps(route,indent=2)+'\n')
s=(p/'record_gamma_one_fourier_converse_702.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-fourier-converse-2','source-gamma-one-ramification-bounds-1'),('SourceGammaOneFourierConverseAudit2','SourceGammaOneRamificationBoundsAudit1'),('SourceGammaOneFourierConverseDependencyAudit2','SourceGammaOneRamificationBoundsDependencyAudit1'),('SOURCE GAMMA ONE FOURIER CONVERSE','SOURCE GAMMA ONE RAMIFICATION BOUNDS'),('gamma-one-fourier-converse-audit-route-702.json','gamma-one-ramification-bounds-audit-route-727.json'),('(2, 2, 10)','(1, 2, 7)'),(' == 2',' == 1'),('all 10 required proof dependencies','all 7 required proof dependencies'),('linterScopes=2','linterScopes=1'),('requiredProofValueEdges=10','requiredProofValueEdges=7'),('modules=2, queries=2','modules=1, queries=2'),('proofEdges=10','proofEdges=7')]:
 assert a in s,a;s=s.replace(a,b)
output('record_gamma_one_ramification_bounds_727.py',s)
print(json.dumps(dict(modules=1,queries=2,edges=7)))