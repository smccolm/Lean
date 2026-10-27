from pathlib import Path
import json,re
p=Path(__file__).parent
mods=['SourceGammaOneFinitePlaceExhaustion'];ns='Dubon2026.SourceFunctionField.GammaOne.'
ths=[ns+n for n in ['exists_analytic_place_eq','place_cusp_or_analytic','finite_fiber_realization']]
extra=[ns+n for n in ['holomorphic_quotient_invariant','holomorphic_realization_of_mem_all_analytic_places','quotient_cusp_represents','holomorphic_quotient_cusp_meromorphic','holomorphic_quotient_cusp_pole_bound','isIntegral_of_mem_all_analytic_places','analyticPlace_j_sub_pos','place_residue_bijective','finiteDimensional_jCoordinateOver','transcendental_jCoordinateOver']]+['Dubon2026.SourceCurve.Place.mem_of_integral_adjoin','Dubon2026.SourceCurve.Place.toValuationSubring_eq_of_forall_mem','Dubon2026.SourceCurve.Place.rationalEval_eq_of_ord_sub_pos']
required=ths+extra;roots=[ths[-1],ths[1]];assert len(required)==16
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime
 assert not (Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')/f.name).exists()
closure=set(mods);todo=mods.copy()
while todo:
 for imp in re.findall(r'^import (\w+)$',(p/(todo.pop()+'.lean')).read_text(encoding='utf-8'),re.M):
  if (p/(imp+'.lean')).exists() and imp not in closure:closure.add(imp);todo.append(imp)
cfg=dict(modules=mods,theorems=ths,constructions=[],queries=ths,proofEdges=required,roots=roots,separatelyAxiomChecked=[],scratchImportClosure=sorted(closure),separateReason='All selected declarations are consumed by actual finite-j place and fiber realization, and by the cusp-or-analytic dichotomy. No surjectivity or integral-equation premise remains.')
def output(n,s):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(s)
output('source-gamma-one-finite-place-exhaustion-1-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneFourierConverseAudit2.lean').read_text(encoding='utf-8');body=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,values in [('modules',mods),('theorems',ths),('constructions',[])]:body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(values),body)
body=body.replace('SOURCE GAMMA ONE FOURIER CONVERSE','SOURCE GAMMA ONE FINITE PLACE EXHAUSTION').replace('Gamma One Fourier Converse','Gamma One Finite Place Exhaustion')
output('SourceGammaOneFinitePlaceExhaustionAudit1.lean',imports+''.join('#print axioms '+n+'\n' for n in ths)+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOneFourierConverseDependencyAudit2.lean').read_text(encoding='utf-8');body=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,values in [('roots',roots),('localModules',sorted(closure)),('required',required)]:body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(values),body)
body=body[:body.index('  logInfo m!')]+'  logInfo m!"SOURCE GAMMA ONE FINITE PLACE EXHAUSTION DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in actual finite-place exhaustion and exact finite-j fiber realization. Only declaration values are traversed. The original finite coordinate and native Dedekind integral closure turn a missing place into an inverse-ideal element; the proved analytic integrality contradicts its nonmembership. Exact residue values give the required upper-half-plane j value. Orbit separation and elliptic/cusp global charts remain. Original chart/period, Hecke/diamond/Picard/H1 arithmetic comparison, all-weight characteristic-zero association and literal higher symmetric-power continuation remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOneFinitePlaceExhaustionDependencyAudit1.lean',imports+body)
route=json.loads((p/'gamma-one-finite-place-exhaustion-route-711.json').read_text(encoding='utf-8'))
output('gamma-one-finite-place-exhaustion-audit-route-711.json',json.dumps(route,indent=2)+'\n')
s=(p/'record_gamma_one_fourier_converse_702.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-fourier-converse-2','source-gamma-one-finite-place-exhaustion-1'),('SourceGammaOneFourierConverseAudit2','SourceGammaOneFinitePlaceExhaustionAudit1'),('SourceGammaOneFourierConverseDependencyAudit2','SourceGammaOneFinitePlaceExhaustionDependencyAudit1'),('SOURCE GAMMA ONE FOURIER CONVERSE','SOURCE GAMMA ONE FINITE PLACE EXHAUSTION'),('gamma-one-fourier-converse-audit-route-702.json','gamma-one-finite-place-exhaustion-audit-route-711.json'),('(2, 2, 10)','(1, 3, 16)'),(' == 2',' == 1'),('all 10 required proof dependencies','all 16 required proof dependencies'),('linterScopes=2','linterScopes=1'),('requiredProofValueEdges=10','requiredProofValueEdges=16'),('modules=2, queries=2','modules=1, queries=3'),('proofEdges=10','proofEdges=16')]:
 assert a in s,a;s=s.replace(a,b)
output('record_gamma_one_finite_place_exhaustion_711.py',s)
print(json.dumps(dict(modules=1,queries=3,edges=16)))