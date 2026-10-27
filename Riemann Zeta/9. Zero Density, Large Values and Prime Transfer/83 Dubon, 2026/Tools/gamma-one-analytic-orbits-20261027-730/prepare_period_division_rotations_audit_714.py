from pathlib import Path
import json,re
p=Path(__file__).parent
mods=['SourcePeriodDivisionRotations'];ns='Dubon2026.SourceFunctionField.GammaOne.DivisionRotations.'
ths=[ns+n for n in ['scale_lattice_eq_of_invariant_powers','exists_rotation_of_division_power']]
extra=['Dubon2026.SourceFunctionField.JOrbitSeparation.g\u2082_scale','Dubon2026.SourceFunctionField.JOrbitSeparation.g\u2083_scale','Dubon2026.SourceFunctionField.LatticeInvariants.lattice_eq_of_invariants']
required=ths+extra;roots=[ths[-1]];assert len(required)==5
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime
 assert not (Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')/f.name).exists()
closure=set(mods);todo=mods.copy()
while todo:
 for imp in re.findall(r'^import (\w+)$',(p/(todo.pop()+'.lean')).read_text(encoding='utf-8'),re.M):
  if (p/(imp+'.lean')).exists() and imp not in closure:closure.add(imp);todo.append(imp)
cfg=dict(modules=mods,theorems=ths,constructions=[],queries=ths,proofEdges=required,roots=roots,separatelyAxiomChecked=[],scratchImportClosure=sorted(closure),separateReason='All selected declarations are consumed by lattice-preserving rotations from division-value powers. Actual division forms and the orbit-separation consumer remain.')
def output(n,s):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(s)
output('source-period-division-rotations-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneFourierConverseAudit2.lean').read_text(encoding='utf-8');body=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,values in [('modules',mods),('theorems',ths),('constructions',[])]:body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(values),body)
body=body.replace('SOURCE GAMMA ONE FOURIER CONVERSE','SOURCE PERIOD DIVISION ROTATIONS').replace('Gamma One Fourier Converse','Period Division Rotations')
output('SourcePeriodDivisionRotationsAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in ths)+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOneFourierConverseDependencyAudit2.lean').read_text(encoding='utf-8');body=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,values in [('roots',roots),('localModules',sorted(closure)),('required',required)]:body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(values),body)
body=body[:body.index('  logInfo m!')]+'  logInfo m!"SOURCE PERIOD DIVISION ROTATIONS DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in lattice-preserving rotations derived from equal division-value powers. Only declaration values are traversed. A complex square root and its root-of-unity equation give unit norm; the existing invariant scaling and lattice uniqueness prove preservation of the actual period lattice. This must still be consumed by actual division-form orbit separation. Original chart/period, Hecke/diamond/Picard/H1 arithmetic comparison, all-weight characteristic-zero association and literal higher symmetric-power continuation remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourcePeriodDivisionRotationsDependencyAudit1.lean',imports+body)
route=json.loads((p/'period-division-rotations-route-714.json').read_text(encoding='utf-8'))
output('period-division-rotations-audit-route-714.json',json.dumps(route,indent=2)+'\n')
s=(p/'record_gamma_one_fourier_converse_702.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-fourier-converse-2','source-period-division-rotations-1'),('SourceGammaOneFourierConverseAudit2','SourcePeriodDivisionRotationsAudit1'),('SourceGammaOneFourierConverseDependencyAudit2','SourcePeriodDivisionRotationsDependencyAudit1'),('SOURCE GAMMA ONE FOURIER CONVERSE','SOURCE PERIOD DIVISION ROTATIONS'),('gamma-one-fourier-converse-audit-route-702.json','period-division-rotations-audit-route-714.json'),('(2, 2, 10)','(1, 2, 5)'),(' == 2',' == 1'),('all 10 required proof dependencies','all 5 required proof dependencies'),('linterScopes=2','linterScopes=1'),('requiredProofValueEdges=10','requiredProofValueEdges=5'),('modules=2, queries=2','modules=1, queries=2'),('proofEdges=10','proofEdges=5')]:
 assert a in s,a;s=s.replace(a,b)
output('record_period_division_rotations_714.py',s)
print(json.dumps(dict(modules=1,queries=2,edges=5)))