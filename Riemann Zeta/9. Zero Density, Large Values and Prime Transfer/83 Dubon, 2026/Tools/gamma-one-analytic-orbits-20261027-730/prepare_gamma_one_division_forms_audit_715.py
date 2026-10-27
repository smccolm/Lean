from pathlib import Path
import json,re
p=Path(__file__).parent
mods=['SourceGammaOneDivisionForms'];ns='Dubon2026.SourceFunctionField.GammaOne.'
ths=[ns+n for n in ['wpNormZ_slash_eq','divisionForm_apply','divisionForm_slash_gamma0']]
defs=[ns+'divisionForm']
extra=['Dubon2026.SourceFricke.'+n for n in ['wpNormZ_slash','mdifferentiable_wpNormZ','isBoundedAtImInfty_wpNormZ']]
required=ths+defs+extra;roots=[ths[1],ths[2]]+defs;assert len(required)==7
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime
 assert not (Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')/f.name).exists()
closure=set(mods);todo=mods.copy()
while todo:
 for imp in re.findall(r'^import (\w+)$',(p/(todo.pop()+'.lean')).read_text(encoding='utf-8'),re.M):
  if (p/(imp+'.lean')).exists() and imp not in closure:closure.add(imp);todo.append(imp)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=[],scratchImportClosure=sorted(closure),separateReason='The actual native division form is a root as well as its analytic evaluation and Gamma0 slash identity. Its holomorphy and cusp bounds are proved from existing torsion-function results. Orbit separation remains.')
def output(n,s):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(s)
output('source-gamma-one-division-forms-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneFourierConverseAudit2.lean').read_text(encoding='utf-8');body=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,values in [('modules',mods),('theorems',ths),('constructions',defs)]:body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(values),body)
body=body.replace('SOURCE GAMMA ONE FOURIER CONVERSE','SOURCE GAMMA ONE DIVISION FORMS').replace('Gamma One Fourier Converse','Gamma One Division Forms')
output('SourceGammaOneDivisionFormsAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in ths+defs)+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOneFourierConverseDependencyAudit2.lean').read_text(encoding='utf-8');body=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,values in [('roots',roots),('localModules',sorted(closure)),('required',required)]:body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(values),body)
body=body[:body.index('  logInfo m!')]+'  logInfo m!"SOURCE GAMMA ONE DIVISION FORMS DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the actual native weight-two Gamma1 division form and its literal analytic value and Gamma0 slash identity. Only declaration values are traversed. Torsion transformation, holomorphy and all-cusp bounds construct the form. Orbit separation remains. Original chart/period, Hecke/diamond/Picard/H1 arithmetic comparison, all-weight characteristic-zero association and literal higher symmetric-power continuation remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOneDivisionFormsDependencyAudit1.lean',imports+body)
route=json.loads((p/'gamma-one-division-forms-route-715.json').read_text(encoding='utf-8'))
output('gamma-one-division-forms-audit-route-715.json',json.dumps(route,indent=2)+'\n')
s=(p/'record_gamma_one_fourier_converse_702.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-fourier-converse-2','source-gamma-one-division-forms-1'),('SourceGammaOneFourierConverseAudit2','SourceGammaOneDivisionFormsAudit1'),('SourceGammaOneFourierConverseDependencyAudit2','SourceGammaOneDivisionFormsDependencyAudit1'),('SOURCE GAMMA ONE FOURIER CONVERSE','SOURCE GAMMA ONE DIVISION FORMS'),('gamma-one-fourier-converse-audit-route-702.json','gamma-one-division-forms-audit-route-715.json'),('(2, 2, 10)','(1, 4, 7)'),(' == 2',' == 1'),('all 10 required proof dependencies','all 7 required proof dependencies'),('linterScopes=2','linterScopes=1'),('requiredProofValueEdges=10','requiredProofValueEdges=7'),('modules=2, queries=2','modules=1, queries=4'),('proofEdges=10','proofEdges=7')]:
 assert a in s,a;s=s.replace(a,b)
output('record_gamma_one_division_forms_715.py',s)
print(json.dumps(dict(modules=1,queries=4,edges=7)))