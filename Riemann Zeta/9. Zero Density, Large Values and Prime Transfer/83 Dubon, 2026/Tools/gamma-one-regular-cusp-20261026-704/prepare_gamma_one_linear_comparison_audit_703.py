from pathlib import Path
import json,re
p=Path(__file__).parent
mods=['SourceGammaOneRegularCuspQExpansion','SourceGammaOneRegularCuspEquiv']
ns='Dubon2026.SourceFunctionField.GammaOne.'
ths=[ns+n for n in ['regularQExpansion_injective','cuspQExpansion_injective','regular_cusp_qExpansion_range_eq','regularCuspEquiv_qExpansion']]
defs=[ns+n for n in ['regularQExpansion','cuspQExpansion','regularCuspEquiv']]
roots=[defs[-1],ths[-1]]
extra=[ns+n for n in ['exists_cuspForm_of_regular_differential','exists_gammaOne_regular_differential_of_coefficients','functionFieldOver_diffQExp_injective','gamma1_regular_of_diffQExp_matches_cusp','regular_differential_cusp_decay','normalized_cusp_qExpansion']]+['Dubon2026.SourceFricke.span_gammaOne_weightTwo_integral_cuspForms_eq_top']
required=ths+defs+extra;assert len(required)==len(set(required))==14
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 assert not (Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')/f.name).exists()
closure=set(mods);todo=mods.copy()
while todo:
 for imp in re.findall(r'^import (\w+)$',(p/(todo.pop()+'.lean')).read_text(encoding='utf-8'),re.M):
  if (p/(imp+'.lean')).exists() and imp not in closure:closure.add(imp);todo.append(imp)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=[],scratchImportClosure=sorted(closure),separateReason='The actual linear equivalence and its exact Fourier identity are the two required outputs. Both are VALUE traversal roots; no type-only dependency is substituted for the construction.')
def output(n,s):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(s)
output('source-gamma-one-linear-comparison-2-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneFourierConverseAudit2.lean').read_text(encoding='utf-8');body=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,values in [('modules',mods),('theorems',ths),('constructions',defs)]:body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(values),body)
body=body.replace('SOURCE GAMMA ONE FOURIER CONVERSE','SOURCE GAMMA ONE LINEAR COMPARISON').replace('Gamma One Fourier Converse','Gamma One Linear Comparison')
output('SourceGammaOneLinearComparisonAudit2.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOneFourierConverseDependencyAudit2.lean').read_text(encoding='utf-8');body=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,values in [('roots',roots),('localModules',sorted(closure)),('required',required)]:body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(values),body)
body=body[:body.index('  logInfo m!')]+'  logInfo m!"SOURCE GAMMA ONE LINEAR COMPARISON DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the actual complex regular-differential/cusp linear equivalence and its literal Fourier identity. Only declaration values are traversed. Both actual realization directions and both injective Fourier maps are consumed. Integral spanning, finite holomorphy, all-cusp decay and exact derivative normalization discharge their advertised assumptions. No dimension certificate or matching witness is assumed. Original Hecke/diamond/Picard/H1 arithmetic comparison, all-weight characteristic-zero association and literal higher symmetric-power continuation remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOneLinearComparisonDependencyAudit2.lean',imports+body)
route=json.loads((p/'gamma-one-linear-comparison-route-703.json').read_text(encoding='utf-8'))
output('gamma-one-linear-comparison-audit-route-703.json',json.dumps(route,indent=2)+'\n')
s=(p/'record_gamma_one_fourier_converse_702.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-fourier-converse-2','source-gamma-one-linear-comparison-2'),('SourceGammaOneFourierConverseAudit2','SourceGammaOneLinearComparisonAudit2'),('SourceGammaOneFourierConverseDependencyAudit2','SourceGammaOneLinearComparisonDependencyAudit2'),('SOURCE GAMMA ONE FOURIER CONVERSE','SOURCE GAMMA ONE LINEAR COMPARISON'),('gamma-one-fourier-converse-audit-route-702.json','gamma-one-linear-comparison-audit-route-703.json'),('(2, 2, 10)','(2, 7, 14)'),('all 10 required proof dependencies','all 14 required proof dependencies'),('requiredProofValueEdges=10','requiredProofValueEdges=14'),('modules=2, queries=2','modules=2, queries=7'),('proofEdges=10','proofEdges=14')]:
 assert a in s,a;s=s.replace(a,b)
output('record_gamma_one_linear_comparison_703.py',s)
print(json.dumps(dict(modules=2,queries=7,edges=14)))