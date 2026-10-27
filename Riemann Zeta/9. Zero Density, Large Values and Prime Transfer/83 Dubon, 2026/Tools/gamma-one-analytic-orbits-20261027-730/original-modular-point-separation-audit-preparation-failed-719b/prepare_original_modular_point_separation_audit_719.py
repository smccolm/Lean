from pathlib import Path
import json,re
p=Path(__file__).parent
mods=['SourceOriginalModularPointSeparation'];ns='Dubon2026.SourceFunctionField.'
ths=[ns+n for n in ['originalPlaceEval_eq_modular_ratio','exists_original_nonvanishing_modular_ratio','exists_gamma0_smul_eq_of_cross_products','exists_original_separating_modular_forms']]
extra=[ns+n for n in ['original_realize_tendsto_residue','exists_original_discriminant_power','AnalyticChart.chart_mem','AnalyticChart.eq_of_center_eq','originalAnalyticPlace_eq_iff_gamma0_orbit','originalAnalyticPlace_j_mem','realize_eventuallyEq_of_ratio']]
required=ths+extra;roots=[ths[-1]];assert len(required)==11
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime
 assert not (Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')/f.name).exists()
closure=set(mods);todo=mods.copy()
while todo:
 for imp in re.findall(r'^import (\w+)$',(p/(todo.pop()+'.lean')).read_text(encoding='utf-8'),re.M):
  if (p/(imp+'.lean')).exists() and imp not in closure:closure.add(imp);todo.append(imp)
cfg=dict(modules=mods,theorems=ths,constructions=[],queries=ths,proofEdges=required,roots=roots,separatelyAxiomChecked=[],scratchImportClosure=sorted(closure),separateReason='The actual Gamma0 separating forms consume residue limits, nonvanishing-denominator modular representations, integral-closure centers and the proved place/orbit dictionary. No new separation premise is introduced.')
def output(n,s):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(s)
output('source-original-modular-point-separation-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneFourierConverseAudit2.lean').read_text(encoding='utf-8');body=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,values in [('modules',mods),('theorems',ths),('constructions',[])]:body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(values),body)
body=body.replace('SOURCE GAMMA ONE FOURIER CONVERSE','SOURCE ORIGINAL MODULAR POINT SEPARATION').replace('Gamma One Fourier Converse','Original Modular Point Separation')
output('SourceOriginalModularPointSeparationAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in ths)+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOneFourierConverseDependencyAudit2.lean').read_text(encoding='utf-8');body=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,values in [('roots',roots),('localModules',sorted(closure)),('required',required)]:body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(values),body)
body=body[:body.index('  logInfo m!')]+'  logInfo m!"SOURCE ORIGINAL MODULAR POINT SEPARATION DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in actual native Gamma0 modular forms separating distinct Gamma0 orbits. Only declaration values are traversed. Existing discriminant-power representations give nowhere-zero denominators; residue limits identify center evaluations, and actual integral-closure centers and the proved place/orbit dictionary produce the orbit matrix. Combination with the Gamma1 within-Gamma0 separation remains. Original chart/period, Hecke/diamond/Picard/H1 arithmetic comparison, all-weight characteristic-zero association and literal higher symmetric-power continuation remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceOriginalModularPointSeparationDependencyAudit1.lean',imports+body)
route=json.loads((p/'original-modular-point-separation-route-719.json').read_text(encoding='utf-8'))
output('original-modular-point-separation-audit-route-719.json',json.dumps(route,indent=2)+'\n')
s=(p/'record_gamma_one_fourier_converse_702.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-fourier-converse-2','source-original-modular-point-separation-1'),('SourceGammaOneFourierConverseAudit2','SourceOriginalModularPointSeparationAudit1'),('SourceGammaOneFourierConverseDependencyAudit2','SourceOriginalModularPointSeparationDependencyAudit1'),('SOURCE GAMMA ONE FOURIER CONVERSE','SOURCE ORIGINAL MODULAR POINT SEPARATION'),('gamma-one-fourier-converse-audit-route-702.json','original-modular-point-separation-audit-route-719.json'),('(2, 2, 10)','(1, 4, 11)'),(' == 2',' == 1'),('all 11 required proof dependencies','all 11 required proof dependencies'),('linterScopes=2','linterScopes=1'),('requiredProofValueEdges=11','requiredProofValueEdges=11'),('modules=2, queries=2','modules=1, queries=4'),('proofEdges=11','proofEdges=11')]:
 assert a in s,a;s=s.replace(a,b)
output('record_original_modular_point_separation_719.py',s)
print(json.dumps(dict(modules=1,queries=4,edges=11)))