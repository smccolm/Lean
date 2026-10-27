from pathlib import Path
import json,re
p=Path(__file__).parent
mods=['SourceGammaOneRegularCuspGerm'];ns='Dubon2026.SourceFunctionField.GammaOne.'
ths=[ns+n for n in ['regularCuspEquiv_eq_normalized','regularCuspEquiv_germ_of_coordinate','exists_regularCuspEquiv_germ']]
extra=[ns+n for n in ['regularCuspEquiv','regularCuspEquiv_qExpansion','normalized_cusp_qExpansion','cuspQExpansion_injective','regular_differential_cusp_form_realization','realize_eventuallyEq_of_ratio','functionFieldOver_isCurveOver','D_jCoordinateOver_ne_zero']]+['Dubon2026.SourceCurve.RegularDifferentialsComparison.exists_smul_eq']
required=ths+extra;roots=[ths[-1]];assert len(required)==12
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime
 assert not (Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')/f.name).exists()
closure=set(mods);todo=mods.copy()
while todo:
 for imp in re.findall(r'^import (\w+)$',(p/(todo.pop()+'.lean')).read_text(encoding='utf-8'),re.M):
  if (p/(imp+'.lean')).exists() and imp not in closure:closure.add(imp);todo.append(imp)
cfg=dict(modules=mods,theorems=ths,constructions=[],queries=ths,proofEdges=required,roots=roots,separatelyAxiomChecked=[],scratchImportClosure=sorted(closure),separateReason='All selected declarations are consumed by the actual analytic germ of every original regular differential, with the exact 2*pi*i factor.')
def output(n,s):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(s)
output('source-gamma-one-period-germ-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneFourierConverseAudit2.lean').read_text(encoding='utf-8');body=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,values in [('modules',mods),('theorems',ths),('constructions',[])]:body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(values),body)
body=body.replace('SOURCE GAMMA ONE FOURIER CONVERSE','SOURCE GAMMA ONE PERIOD GERM').replace('Gamma One Fourier Converse','Gamma One Period Germ')
output('SourceGammaOnePeriodGermAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in ths)+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOneFourierConverseDependencyAudit2.lean').read_text(encoding='utf-8');body=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,values in [('roots',roots),('localModules',sorted(closure)),('required',required)]:body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(values),body)
body=body[:body.index('  logInfo m!')]+'  logInfo m!"SOURCE GAMMA ONE PERIOD GERM DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the analytic integrand of every original regular differential. Only declaration values are traversed. The actual Fourier-normalized equivalence is identified with the constructed native cusp form; the exact quotient identity gives its analytic germ with the precise 2*pi*i factor. Original chart/period, Hecke/diamond/Picard/H1 arithmetic comparison, all-weight characteristic-zero association and literal higher symmetric-power continuation remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOnePeriodGermDependencyAudit1.lean',imports+body)
route=json.loads((p/'gamma-one-period-germ-route-705.json').read_text(encoding='utf-8'))
output('gamma-one-period-germ-audit-route-705.json',json.dumps(route,indent=2)+'\n')
s=(p/'record_gamma_one_fourier_converse_702.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-fourier-converse-2','source-gamma-one-period-germ-1'),('SourceGammaOneFourierConverseAudit2','SourceGammaOnePeriodGermAudit1'),('SourceGammaOneFourierConverseDependencyAudit2','SourceGammaOnePeriodGermDependencyAudit1'),('SOURCE GAMMA ONE FOURIER CONVERSE','SOURCE GAMMA ONE PERIOD GERM'),('gamma-one-fourier-converse-audit-route-702.json','gamma-one-period-germ-audit-route-705.json'),('(2, 2, 10)','(1, 3, 12)'),(' == 2',' == 1'),('all 10 required proof dependencies','all 12 required proof dependencies'),('linterScopes=2','linterScopes=1'),('requiredProofValueEdges=10','requiredProofValueEdges=12'),('modules=2, queries=2','modules=1, queries=3'),('proofEdges=10','proofEdges=12')]:
 assert a in s,a;s=s.replace(a,b)
output('record_gamma_one_period_germ_705.py',s)
print(json.dumps(dict(modules=1,queries=3,edges=12)))