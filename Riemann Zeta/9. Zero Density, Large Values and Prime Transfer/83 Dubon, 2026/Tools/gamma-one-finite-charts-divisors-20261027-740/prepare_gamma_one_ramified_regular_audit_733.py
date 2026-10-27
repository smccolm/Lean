from pathlib import Path
import json,re
p=Path(__file__).parent
mods=['SourceGammaOneEllipticFibers','SourceGammaOneRamifiedRegularParameter','SourceGammaOneRamifiedRegularOrder']
ns='Dubon2026.SourceFunctionField.GammaOne.'
ths=[ns+n for n in ['exists_stabilizer_multiplier','place_eq_of_coord_power_eq','ramifiedPlace_zero','ramifiedPlace_regular_analytic','ramifiedPlace_regular_order']]
cons=[ns+'ramifiedPlace'];queries=ths+cons;roots=ths
required=queries+[ns+'two_mul_ramification_eq_stabilizer_card',ns+'analyticPlace_smul_plusMinus','Dubon2026.SourceFunctionField.EllipticCoordinate.multiplier_eq_inv_square','Dubon2026.SourceFunctionField.PowerDescent.analyticAt_root_composite',ns+'placeEval_meromorphicOrderAt',ns+'placeEval_analyticAt_iff']
assert len(required)==12
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime
 assert not (Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')/f.name).exists()
closure=set(mods);todo=mods.copy()
while todo:
 for imp in re.findall(r'^import (\w+)$',(p/(todo.pop()+'.lean')).read_text(encoding='utf-8'),re.M):
  if (p/(imp+'.lean')).exists() and imp not in closure:closure.add(imp);todo.append(imp)
cfg=dict(modules=mods,theorems=ths,constructions=cons,queries=queries,proofEdges=required,roots=roots,separatelyAxiomChecked=[],scratchImportClosure=sorted(closure),separateReason='Exact all-level Gamma1 ramification supplies every stabilizer multiplier and actual-place invariance discharges power-fiber invariance. Analytic descent and the actual residue-value order identity give analytic regular values of exactly the normalized valuation order.')
def output(n,s):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(s)
output('source-gamma-one-ramified-regular-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneFourierConverseAudit2.lean').read_text(encoding='utf-8');body=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,values in [('modules',mods),('theorems',ths),('constructions',cons)]:body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(values),body)
body=body.replace('SOURCE GAMMA ONE FOURIER CONVERSE','SOURCE GAMMA ONE RAMIFIED REGULAR').replace('Gamma One Fourier Converse','Gamma One Ramified Regular')
output('SourceGammaOneRamifiedRegularAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in queries)+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOneFourierConverseDependencyAudit2.lean').read_text(encoding='utf-8');body=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,values in [('roots',roots),('localModules',sorted(closure)),('required',required)]:body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(values),body)
body=body[:body.index('  logInfo m!')]+'  logInfo m!"SOURCE GAMMA ONE RAMIFIED REGULAR DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in actual Gamma1 ramified regular descent. Only declaration values are traversed. Exact ramification and actual place invariance discharge the power-fiber invariance premise. Existing analytic descent gives analytic residue values; the actual order identity cancels the positive ramification factor. All nonzero levels and elliptic points are covered. Common chart neighborhoods, cusp/global charts, actual period and Hecke/diamond/Picard/H1 arithmetic comparison, all-weight characteristic-zero association and literal higher symmetric-power continuation remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOneRamifiedRegularDependencyAudit1.lean',imports+body)
route=json.loads((p/'gamma-one-ramified-regular-route-733.json').read_text(encoding='utf-8'))
output('gamma-one-ramified-regular-audit-route-733.json',json.dumps(route,indent=2)+'\n')
s=(p/'record_gamma_one_fourier_converse_702.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-fourier-converse-2','source-gamma-one-ramified-regular-1'),('SourceGammaOneFourierConverseAudit2','SourceGammaOneRamifiedRegularAudit1'),('SourceGammaOneFourierConverseDependencyAudit2','SourceGammaOneRamifiedRegularDependencyAudit1'),('SOURCE GAMMA ONE FOURIER CONVERSE','SOURCE GAMMA ONE RAMIFIED REGULAR'),('gamma-one-fourier-converse-audit-route-702.json','gamma-one-ramified-regular-audit-route-733.json'),('(2, 2, 10)','(3, 6, 12)'),(' == 2',' == 3'),('all 10 required proof dependencies','all 12 required proof dependencies'),('linterScopes=2','linterScopes=3'),('requiredProofValueEdges=10','requiredProofValueEdges=12'),('modules=2, queries=2','modules=3, queries=6'),('proofEdges=10','proofEdges=12'),('20261026','20261027'),('2026-10-26','2026-10-27')]:
 assert a in s,a;s=s.replace(a,b)
output('record_gamma_one_ramified_regular_733.py',s)
s=(p/'SourceGammaOneGenericFiberCountScratchOwnership729.lean').read_text(encoding='utf-8')
s=s.replace('import SourceGammaOneGenericFiberCount',''.join('import '+m+'\n' for m in mods).rstrip())
s=s.replace('#[`SourceGammaOneGenericFiberCount]',arr(mods))
output('SourceGammaOneRamifiedRegularScratchOwnership733.lean',s)
print(json.dumps(dict(modules=3,queries=6,edges=12)))
