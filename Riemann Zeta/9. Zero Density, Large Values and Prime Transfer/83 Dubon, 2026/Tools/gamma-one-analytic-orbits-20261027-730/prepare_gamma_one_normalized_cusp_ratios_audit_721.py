from pathlib import Path
import json,re
p=Path(__file__).parent
mods=['SourceGammaOneNormalizedCuspRatios'];ns='Dubon2026.SourceFunctionField.GammaOne.'
ths=[ns+n for n in ['normalized_cusp_ratio_mem']]
extra=['Dubon2026.SourceFricke.span_gammaOne_integral_cuspForms_eq_top',ns+'div_mem_qExpFunctionFieldC','Dubon2026.SourceDifferential.algebraMap_laurentSeries_apply_alt']
required=ths+extra;roots=ths;assert len(required)==4
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime
 assert not (Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')/f.name).exists()
closure=set(mods);todo=mods.copy()
while todo:
 for imp in re.findall(r'^import (\w+)$',(p/(todo.pop()+'.lean')).read_text(encoding='utf-8'),re.M):
  if (p/(imp+'.lean')).exists() and imp not in closure:closure.add(imp);todo.append(imp)
cfg=dict(modules=mods,theorems=ths,constructions=[],queries=ths,proofEdges=required,roots=roots,separatelyAxiomChecked=[],scratchImportClosure=sorted(closure),separateReason='The literal normalized cusp ratio consumes integral cusp spanning and the existing integral-ratio field construction.')
def output(n,s):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(s)
output('source-gamma-one-normalized-cusp-ratios-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneFourierConverseAudit2.lean').read_text(encoding='utf-8');body=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,values in [('modules',mods),('theorems',ths),('constructions',[])]:body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(values),body)
body=body.replace('SOURCE GAMMA ONE FOURIER CONVERSE','SOURCE GAMMA ONE NORMALIZED CUSP RATIOS').replace('Gamma One Fourier Converse','Gamma One Normalized Cusp Ratios')
output('SourceGammaOneNormalizedCuspRatiosAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in ths)+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOneFourierConverseDependencyAudit2.lean').read_text(encoding='utf-8');body=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,values in [('roots',roots),('localModules',sorted(closure)),('required',required)]:body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(values),body)
body=body[:body.index('  logInfo m!')]+'  logInfo m!"SOURCE GAMMA ONE NORMALIZED CUSP RATIOS DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in actual complex Gamma1 cusp ratios in the original integral-ratio function field. Only declaration values are traversed. Existing integral cusp spanning and literal field membership are consumed. Arbitrary modular ratio membership and exact analytic-place orbit identification remain. Original chart/period, Hecke/diamond/Picard/H1 arithmetic comparison, all-weight characteristic-zero association and literal higher symmetric-power continuation remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOneNormalizedCuspRatiosDependencyAudit1.lean',imports+body)
route=json.loads((p/'gamma-one-normalized-cusp-ratios-route-721.json').read_text(encoding='utf-8'))
output('gamma-one-normalized-cusp-ratios-audit-route-721.json',json.dumps(route,indent=2)+'\n')
s=(p/'record_gamma_one_fourier_converse_702.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-fourier-converse-2','source-gamma-one-normalized-cusp-ratios-1'),('SourceGammaOneFourierConverseAudit2','SourceGammaOneNormalizedCuspRatiosAudit1'),('SourceGammaOneFourierConverseDependencyAudit2','SourceGammaOneNormalizedCuspRatiosDependencyAudit1'),('SOURCE GAMMA ONE FOURIER CONVERSE','SOURCE GAMMA ONE NORMALIZED CUSP RATIOS'),('gamma-one-fourier-converse-audit-route-702.json','gamma-one-normalized-cusp-ratios-audit-route-721.json'),('(2, 2, 10)','(1, 1, 4)'),(' == 2',' == 1'),('all 10 required proof dependencies','all 4 required proof dependencies'),('linterScopes=2','linterScopes=1'),('requiredProofValueEdges=10','requiredProofValueEdges=4'),('modules=2, queries=2','modules=1, queries=1'),('proofEdges=10','proofEdges=4')]:
 assert a in s,a;s=s.replace(a,b)
output('record_gamma_one_normalized_cusp_ratios_721.py',s)
print(json.dumps(dict(modules=1,queries=1,edges=4)))