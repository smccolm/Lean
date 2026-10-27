from pathlib import Path
import json,re
p=Path(__file__).parent
mods=['SourceGammaOnePlusMinus'];ns='Dubon2026.SourceFunctionField.GammaOne.'
ths=[ns+n for n in ['le_plusMinus', 'neg_one_mem_plusMinus', 'mem_plusMinus_iff', 'exists_gamma_smul_eq_of_mem_plusMinus', 'analyticPlace_smul_plusMinus', 'two_le_card_stabilizer_plusMinus', 'plusMinus_stabilizer_card_dvd_two_mul_ramification']]
cons=[ns+'plusMinus',ns+'plusMinusFiniteIndex']
extra=cons+['Dubon2026.SourceFunctionField.SubgroupStabilizer.main',ns+'analyticPlace_smul',ns+'functionFieldOver_modular_ratio']
required=ths+extra;roots=ths+cons;assert len(required)==12
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime
 assert not (Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')/f.name).exists()
closure=set(mods);todo=mods.copy()
while todo:
 for imp in re.findall(r'^import (\w+)$',(p/(todo.pop()+'.lean')).read_text(encoding='utf-8'),re.M):
  if (p/(imp+'.lean')).exists() and imp not in closure:closure.add(imp);todo.append(imp)
cfg=dict(modules=mods,theorems=ths,constructions=cons,queries=ths+cons,proofEdges=required,roots=roots,separatelyAxiomChecked=[],scratchImportClosure=sorted(closure),separateReason='The central-sign enlargement preserves actual orbits and analytic places and supplies stabilizer divisibility for the original field uniformizer.')
def output(n,s):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(s)
output('source-gamma-one-plus-minus-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneFourierConverseAudit2.lean').read_text(encoding='utf-8');body=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,values in [('modules',mods),('theorems',ths),('constructions',cons)]:body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(values),body)
body=body.replace('SOURCE GAMMA ONE FOURIER CONVERSE','SOURCE GAMMA ONE PLUS MINUS').replace('Gamma One Fourier Converse','Gamma One Plus Minus')
output('SourceGammaOnePlusMinusAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in ths+cons)+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOneFourierConverseDependencyAudit2.lean').read_text(encoding='utf-8');body=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,values in [('roots',roots),('localModules',sorted(closure)),('required',required)]:body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(values),body)
body=body[:body.index('  logInfo m!')]+'  logInfo m!"SOURCE GAMMA ONE PLUS MINUS DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the actual central-sign subgroup enlargement, identical point orbits and analytic places, and its stabilizer divisibility for the original field uniformizer. Only declaration values are traversed. The field is unchanged and the factor of two is retained. Exact elliptic ramification and global charts remain. Original chart/period, Hecke/diamond/Picard/H1 arithmetic comparison, all-weight characteristic-zero association and literal higher symmetric-power continuation remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOnePlusMinusDependencyAudit1.lean',imports+body)
route=json.loads((p/'gamma-one-plus-minus-route-726.json').read_text(encoding='utf-8'))
output('gamma-one-plus-minus-audit-route-726.json',json.dumps(route,indent=2)+'\n')
s=(p/'record_gamma_one_fourier_converse_702.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-fourier-converse-2','source-gamma-one-plus-minus-1'),('SourceGammaOneFourierConverseAudit2','SourceGammaOnePlusMinusAudit1'),('SourceGammaOneFourierConverseDependencyAudit2','SourceGammaOnePlusMinusDependencyAudit1'),('SOURCE GAMMA ONE FOURIER CONVERSE','SOURCE GAMMA ONE PLUS MINUS'),('gamma-one-fourier-converse-audit-route-702.json','gamma-one-plus-minus-audit-route-726.json'),('(2, 2, 10)','(1, 9, 12)'),(' == 2',' == 1'),('all 10 required proof dependencies','all 12 required proof dependencies'),('linterScopes=2','linterScopes=1'),('requiredProofValueEdges=10','requiredProofValueEdges=12'),('modules=2, queries=2','modules=1, queries=9'),('proofEdges=10','proofEdges=12')]:
 assert a in s,a;s=s.replace(a,b)
output('record_gamma_one_plus_minus_726.py',s)
print(json.dumps(dict(modules=1,queries=9,edges=12)))