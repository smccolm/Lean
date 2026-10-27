from pathlib import Path
import json,re
p=Path(__file__).parent
mods=['SourceGammaOneOrbitCounting'];ns='Dubon2026.SourceFunctionField.GammaOne.OrbitCounting.'
ths=[ns+n for n in ['card_stabilizer_subgroup', 'relIndex_stabilizer_smul_of_mem', 'relIndex_stabilizer_mul_card_stabilizer', 'finite_orbitRelQuotient_orbit', 'exists_smul_out_eq', 'finsum_relIndex_stabilizer_eq_index']]
extra=[]
required=ths+extra;roots=ths;assert len(required)==6
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime
 assert not (Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')/f.name).exists()
closure=set(mods);todo=mods.copy()
while todo:
 for imp in re.findall(r'^import (\w+)$',(p/(todo.pop()+'.lean')).read_text(encoding='utf-8'),re.M):
  if (p/(imp+'.lean')).exists() and imp not in closure:closure.add(imp);todo.append(imp)
cfg=dict(modules=mods,theorems=ths,constructions=[],queries=ths,proofEdges=required,roots=roots,separatelyAxiomChecked=[],scratchImportClosure=sorted(closure),separateReason='weighted subgroup orbit indices equal to the finite subgroup index, with actual quotient fibers and stabilizer cardinalities. No ramification or field degree is assumed.')
def output(n,s):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(s)
output('source-gamma-one-orbit-counting-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneFourierConverseAudit2.lean').read_text(encoding='utf-8');body=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,values in [('modules',mods),('theorems',ths),('constructions',[])]:body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(values),body)
body=body.replace('SOURCE GAMMA ONE FOURIER CONVERSE','SOURCE GAMMA ONE ORBIT COUNTING').replace('Gamma One Fourier Converse','Gamma One Orbit Counting')
output('SourceGammaOneOrbitCountingAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in ths)+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOneFourierConverseDependencyAudit2.lean').read_text(encoding='utf-8');body=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,values in [('roots',roots),('localModules',sorted(closure)),('required',required)]:body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(values),body)
body=body[:body.index('  logInfo m!')]+'  logInfo m!"SOURCE GAMMA ONE ORBIT COUNTING DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in weighted subgroup orbit indices equal to the finite subgroup index, with actual quotient fibers and stabilizer cardinalities. No ramification or field degree is assumed. Only declaration values are traversed. Exact elliptic ramification and global charts remain. Original chart/period, Hecke/diamond/Picard/H1 arithmetic comparison, all-weight characteristic-zero association and literal higher symmetric-power continuation remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOneOrbitCountingDependencyAudit1.lean',imports+body)
route=json.loads((p/'gamma-one-orbit-counting-route-725.json').read_text(encoding='utf-8'))
output('gamma-one-orbit-counting-audit-route-725.json',json.dumps(route,indent=2)+'\n')
s=(p/'record_gamma_one_fourier_converse_702.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-fourier-converse-2','source-gamma-one-orbit-counting-1'),('SourceGammaOneFourierConverseAudit2','SourceGammaOneOrbitCountingAudit1'),('SourceGammaOneFourierConverseDependencyAudit2','SourceGammaOneOrbitCountingDependencyAudit1'),('SOURCE GAMMA ONE FOURIER CONVERSE','SOURCE GAMMA ONE ORBIT COUNTING'),('gamma-one-fourier-converse-audit-route-702.json','gamma-one-orbit-counting-audit-route-725.json'),('(2, 2, 10)','(1, 6, 6)'),(' == 2',' == 1'),('all 10 required proof dependencies','all 6 required proof dependencies'),('linterScopes=2','linterScopes=1'),('requiredProofValueEdges=10','requiredProofValueEdges=6'),('modules=2, queries=2','modules=1, queries=6'),('proofEdges=10','proofEdges=6')]:
 assert a in s,a;s=s.replace(a,b)
output('record_gamma_one_orbit_counting_725.py',s)
print(json.dumps(dict(modules=1,queries=6,edges=6)))