from pathlib import Path
import json,re
p=Path(__file__).parent
mods=['SourceGammaOneDiamondSeparation'];ns='Dubon2026.SourceFunctionField.GammaOne.'
ths=[ns+n for n in ['exists_gamma1_smul_eq_of_cross_products','exists_separating_forms_of_gamma0_orbit']]
extra=[ns+n for n in ['divisionForm','divisionForm_apply','divisionForm_slash_gamma0','exists_gamma1_smul_eq_of_division_power']]+['Dubon2026.SourceFunctionField.ModularNormPolynomial.restrict','Dubon2026.SourceEllipticPeriod.gTwo_ofTau','Dubon2026.SourceEllipticPeriod.gThree_ofTau','ModularForm.pow']
required=ths+extra;roots=[ths[-1]];assert len(required)==10
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime
 assert not (Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')/f.name).exists()
closure=set(mods);todo=mods.copy()
while todo:
 for imp in re.findall(r'^import (\w+)$',(p/(todo.pop()+'.lean')).read_text(encoding='utf-8'),re.M):
  if (p/(imp+'.lean')).exists() and imp not in closure:closure.add(imp);todo.append(imp)
cfg=dict(modules=mods,theorems=ths,constructions=[],queries=ths,proofEdges=required,roots=roots,separatelyAxiomChecked=[],scratchImportClosure=sorted(closure),separateReason='The actual separating forms consume all selected division-form and division-power theorems. The remaining non-Gamma0-related case is separate.')
def output(n,s):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(s)
output('source-gamma-one-diamond-separation-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneFourierConverseAudit2.lean').read_text(encoding='utf-8');body=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,values in [('modules',mods),('theorems',ths),('constructions',[])]:body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(values),body)
body=body.replace('SOURCE GAMMA ONE FOURIER CONVERSE','SOURCE GAMMA ONE DIAMOND SEPARATION').replace('Gamma One Fourier Converse','Gamma One Diamond Separation')
output('SourceGammaOneDiamondSeparationAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in ths)+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOneFourierConverseDependencyAudit2.lean').read_text(encoding='utf-8');body=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,values in [('roots',roots),('localModules',sorted(closure)),('required',required)]:body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(values),body)
body=body[:body.index('  logInfo m!')]+'  logInfo m!"SOURCE GAMMA ONE DIAMOND SEPARATION DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in actual native Gamma1 forms separating points in the same Gamma0 orbit. Only declaration values are traversed. Native squares and cubes, existing restriction, actual division-form slash law and E4/E6 anchors derive the division-value hypotheses, including elliptic points and level one. Non-Gamma0-related points remain. Original chart/period, Hecke/diamond/Picard/H1 arithmetic comparison, all-weight characteristic-zero association and literal higher symmetric-power continuation remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOneDiamondSeparationDependencyAudit1.lean',imports+body)
route=json.loads((p/'gamma-one-diamond-separation-route-718.json').read_text(encoding='utf-8'))
output('gamma-one-diamond-separation-audit-route-718.json',json.dumps(route,indent=2)+'\n')
s=(p/'record_gamma_one_fourier_converse_702.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-fourier-converse-2','source-gamma-one-diamond-separation-1'),('SourceGammaOneFourierConverseAudit2','SourceGammaOneDiamondSeparationAudit1'),('SourceGammaOneFourierConverseDependencyAudit2','SourceGammaOneDiamondSeparationDependencyAudit1'),('SOURCE GAMMA ONE FOURIER CONVERSE','SOURCE GAMMA ONE DIAMOND SEPARATION'),('gamma-one-fourier-converse-audit-route-702.json','gamma-one-diamond-separation-audit-route-718.json'),('(2, 2, 10)','(1, 2, 10)'),(' == 2',' == 1'),('all 10 required proof dependencies','all 10 required proof dependencies'),('linterScopes=2','linterScopes=1'),('requiredProofValueEdges=10','requiredProofValueEdges=10'),('modules=2, queries=2','modules=1, queries=2'),('proofEdges=10','proofEdges=10')]:
 assert a in s,a;s=s.replace(a,b)
output('record_gamma_one_diamond_separation_718.py',s)
print(json.dumps(dict(modules=1,queries=2,edges=10)))