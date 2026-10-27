from pathlib import Path
import json,re
p=Path(__file__).parent
mods=['SourceGammaOneAnalyticPlaceInvariance','SourceGammaOneStabilizerRamification'];ns='Dubon2026.SourceFunctionField.GammaOne.'
ths=[ns+n for n in ['realize_smul_eventuallyEq','analyticOrder_smul','analyticPlace_smul','stabilizer_card_dvd_two_mul_ramification']]
extra=[ns+n for n in ['functionFieldOver_modular_ratio','realize_eq_div','analyticPlace_mem_iff','analyticPlace_order','realize_eventuallyEq_of_ratio']]+['Dubon2026.SourceFunctionField.SubgroupStabilizer.main']
required=ths+extra;roots=[ths[2],ths[3]];assert len(required)==10
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime
 assert not (Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')/f.name).exists()
closure=set(mods);todo=mods.copy()
while todo:
 for imp in re.findall(r'^import (\w+)$',(p/(todo.pop()+'.lean')).read_text(encoding='utf-8'),re.M):
  if (p/(imp+'.lean')).exists() and imp not in closure:closure.add(imp);todo.append(imp)
cfg=dict(modules=mods,theorems=ths,constructions=[],queries=ths,proofEdges=required,roots=roots,separatelyAxiomChecked=[],scratchImportClosure=sorted(closure),separateReason='All selected declarations are consumed by actual analytic-place invariance or by the subgroup stabilizer divisibility bound for the actual uniformizer.')
def output(n,s):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(s)
output('source-gamma-one-place-invariance-2-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneFourierConverseAudit2.lean').read_text(encoding='utf-8');body=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,values in [('modules',mods),('theorems',ths),('constructions',[])]:body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(values),body)
body=body.replace('SOURCE GAMMA ONE FOURIER CONVERSE','SOURCE GAMMA ONE PLACE INVARIANCE').replace('Gamma One Fourier Converse','Gamma One Place Invariance')
output('SourceGammaOnePlaceInvarianceAudit2.lean',imports+''.join('#print axioms '+n+'\n' for n in ths)+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOneFourierConverseDependencyAudit2.lean').read_text(encoding='utf-8');body=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,values in [('roots',roots),('localModules',sorted(closure)),('required',required)]:body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(values),body)
body=body[:body.index('  logInfo m!')]+'  logInfo m!"SOURCE GAMMA ONE PLACE INVARIANCE DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in actual place invariance and the stabilizer divisibility bound. Only declaration values are traversed. The original modular quotient gives an invariant germ; native Mobius order invariance identifies actual normalized places. The actual uniformizer and its exact normalized order feed the existing subgroup stabilizer theorem. The reverse ramification bound and orbit separation remain. Original chart/period, Hecke/diamond/Picard/H1 arithmetic comparison, all-weight characteristic-zero association and literal higher symmetric-power continuation remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOnePlaceInvarianceDependencyAudit2.lean',imports+body)
route=json.loads((p/'gamma-one-place-invariance-route-713.json').read_text(encoding='utf-8'))
output('gamma-one-place-invariance-audit-route-713.json',json.dumps(route,indent=2)+'\n')
s=(p/'record_gamma_one_fourier_converse_702.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-fourier-converse-2','source-gamma-one-place-invariance-2'),('SourceGammaOneFourierConverseAudit2','SourceGammaOnePlaceInvarianceAudit2'),('SourceGammaOneFourierConverseDependencyAudit2','SourceGammaOnePlaceInvarianceDependencyAudit2'),('SOURCE GAMMA ONE FOURIER CONVERSE','SOURCE GAMMA ONE PLACE INVARIANCE'),('gamma-one-fourier-converse-audit-route-702.json','gamma-one-place-invariance-audit-route-713.json'),('(2, 2, 10)','(2, 4, 10)'),(' == 2',' == 2'),('all 10 required proof dependencies','all 10 required proof dependencies'),('linterScopes=2','linterScopes=2'),('requiredProofValueEdges=10','requiredProofValueEdges=10'),('modules=2, queries=2','modules=2, queries=4'),('proofEdges=10','proofEdges=10')]:
 assert a in s,a;s=s.replace(a,b)
output('record_gamma_one_place_invariance_713.py',s)
print(json.dumps(dict(modules=2,queries=4,edges=10)))