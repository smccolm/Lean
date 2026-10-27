from pathlib import Path
import json,re,hashlib
p=Path(__file__).parent
mods=['SourceGammaOneCuspFourierNormalization','SourceGammaOneRegularFourierRealization']
ns='Dubon2026.SourceFunctionField.GammaOne.'
ths=[ns+'normalized_cusp_qExpansion',ns+'exists_cuspForm_of_regular_differential']
extra=[ns+'regular_differential_cusp_form_realization','Dubon2026.SourceFunctionField.ModularQDerivative.qEuler_jqModC_mul_discriminant','Dubon2026.SourceDifferential.span_D_eq_top_of_transcendental',ns+'finiteDimensional_jCoordinateOver',ns+'transcendental_jCoordinateOver','Dubon2026.SourceDifferential.diffQExp_smul_D',ns+'exists_holomorphic_differential',ns+'regular_differential_cusp_decay']
required=ths+extra;roots=[ths[-1]]
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime
 assert not (Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')/f.name).exists()
closure=set(mods);todo=mods.copy()
while todo:
 for imp in re.findall(r'^import (\w+)$',(p/(todo.pop()+'.lean')).read_text(encoding='utf-8'),re.M):
  if (p/(imp+'.lean')).exists() and imp not in closure:closure.add(imp);todo.append(imp)
cfg=dict(modules=mods,theorems=ths,constructions=[],queries=ths,proofEdges=required,roots=roots,separatelyAxiomChecked=[],scratchImportClosure=sorted(closure),separateReason='Both declarations are required by the exact Fourier realization of every original complex regular differential.')
def output(n,s):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(s)
output('source-gamma-one-fourier-converse-2-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneCuspVanishingAudit10.lean').read_text(encoding='utf-8');body=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,values in [('modules',mods),('theorems',ths),('constructions',[])]:body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(values),body)
body=body.replace('SOURCE GAMMA ONE CUSP VANISHING','SOURCE GAMMA ONE FOURIER CONVERSE').replace('Gamma One Cusp Vanishing','Gamma One Fourier Converse')
output('SourceGammaOneFourierConverseAudit2.lean',imports+''.join('#print axioms '+n+'\n' for n in ths)+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOneCuspVanishingDependencyAudit10.lean').read_text(encoding='utf-8');body=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,values in [('roots',roots),('localModules',sorted(closure)),('required',required)]:body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(values),body)
body=body[:body.index('  logInfo m!')]+'  logInfo m!"SOURCE GAMMA ONE FOURIER CONVERSE DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the exact native cusp-form Fourier realization of every original complex regular differential. Only declaration values are traversed. The existing j-differential spanning theorem supplies the coefficient; finite holomorphy and all-cusp decay supply the actual form; the literal q-Euler modular identity fixes its Fourier series after the explicit 2*pi*i normalization. Coefficient transport, Hecke/diamond arithmetic comparison and literal higher symmetric-power continuation remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOneFourierConverseDependencyAudit2.lean',imports+body)
route=json.loads((p/'gamma-one-fourier-converse-route-702.json').read_text(encoding='utf-8'))
route['remaining']='Coefficient-field transport, complete linear differential/cusp equivalence and original Hecke/diamond/Picard/H1 arithmetic comparison, all-weight characteristic-zero association and literal higher symmetric-power continuation remain. 16/20; DUB-17--20 OPEN.'
output('gamma-one-fourier-converse-audit-route-702.json',json.dumps(route,indent=2)+'\n')
s=(p/'record_gamma_one_cusp_vanishing_701.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-cusp-vanishing-10','source-gamma-one-fourier-converse-2'),('SourceGammaOneCuspVanishingAudit10','SourceGammaOneFourierConverseAudit2'),('SourceGammaOneCuspVanishingDependencyAudit10','SourceGammaOneFourierConverseDependencyAudit2'),('SOURCE GAMMA ONE CUSP VANISHING','SOURCE GAMMA ONE FOURIER CONVERSE'),('gamma-one-cusp-vanishing-audit-route-701.json','gamma-one-fourier-converse-audit-route-702.json'),('(10, 36, 46)','(2, 2, 10)'),(' == 10',' == 2'),('all 46 required proof dependencies','all 10 required proof dependencies'),('linterScopes=10','linterScopes=2'),('requiredProofValueEdges=46','requiredProofValueEdges=10'),('modules=10, queries=36','modules=2, queries=2'),('proofEdges=46','proofEdges=10')]:
 assert a in s,a;s=s.replace(a,b)
output('record_gamma_one_fourier_converse_702.py',s)
print(json.dumps(dict(modules=2,queries=2,edges=10)))