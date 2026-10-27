from pathlib import Path
import json,re
p=Path(__file__).parent
mods=['SourceGammaOneHolomorphicFunctions','SourceGammaOneQuotientCuspSeries','SourceGammaOneAnalyticIntegrality'];ns='Dubon2026.SourceFunctionField.GammaOne.'
ths=[ns+n for n in ['holomorphic_quotient_invariant','holomorphic_realization_of_mem_all_analytic_places','quotient_cusp_represents','holomorphic_quotient_cusp_meromorphic','holomorphic_quotient_cusp_pole_bound','isIntegral_of_mem_all_analytic_places']]
extra=[ns+n for n in ['functionFieldOver_modular_ratio','analyticPlace_mem_iff','meromorphicAt_realize','realize_eventuallyEq_of_ratio']]+['Dubon2026.SourceFunctionField.HolomorphicQuotient.exists_mdifferentiable_mul_eq','Dubon2026.SourceFricke.exists_bounded_mul_discriminant_of_meromorphic','Dubon2026.SourceFricke.exists_fraction_and_monic_j_of_principal_invariant','Dubon2026.SourceFunctionField.CuspTaylor.Represents.isIntegral_of_monic_relation','Dubon2026.SourceFunctionField.represents_jqNModC','Dubon2026.SourceFunctionField.isIntegral_adjoin_subfield']
required=ths+extra;roots=[ths[-1]];assert len(required)==16
for m in mods:
 f=p/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime
 assert not (Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')/f.name).exists()
closure=set(mods);todo=mods.copy()
while todo:
 for imp in re.findall(r'^import (\w+)$',(p/(todo.pop()+'.lean')).read_text(encoding='utf-8'),re.M):
  if (p/(imp+'.lean')).exists() and imp not in closure:closure.add(imp);todo.append(imp)
cfg=dict(modules=mods,theorems=ths,constructions=[],queries=ths,proofEdges=required,roots=roots,separatelyAxiomChecked=[],scratchImportClosure=sorted(closure),separateReason='All selected declarations are consumed by integrality over the original C[j] of actual field elements regular at every actual analytic place.')
def output(n,s):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(s)
output('source-gamma-one-analytic-integrality-3-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneFourierConverseAudit2.lean').read_text(encoding='utf-8');body=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,values in [('modules',mods),('theorems',ths),('constructions',[])]:body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(values),body)
body=body.replace('SOURCE GAMMA ONE FOURIER CONVERSE','SOURCE GAMMA ONE ANALYTIC INTEGRALITY').replace('Gamma One Fourier Converse','Gamma One Analytic Integrality')
output('SourceGammaOneAnalyticIntegralityAudit3.lean',imports+''.join('#print axioms '+n+'\n' for n in ths)+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOneFourierConverseDependencyAudit2.lean').read_text(encoding='utf-8');body=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,values in [('roots',roots),('localModules',sorted(closure)),('required',required)]:body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(values),body)
body=body[:body.index('  logInfo m!')]+'  logInfo m!"SOURCE GAMMA ONE ANALYTIC INTEGRALITY DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in integrality of the actual original field element over C[j]. Only declaration values are traversed. Actual analytic-place regularity derives a holomorphic invariant quotient, literal cusp representatives and translated pole bounds; the existing monic modular-orbit relation transfers through the literal Laurent representation. Finite-place exhaustion still must consume this theorem. Original chart/period, Hecke/diamond/Picard/H1 arithmetic comparison, all-weight characteristic-zero association and literal higher symmetric-power continuation remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOneAnalyticIntegralityDependencyAudit3.lean',imports+body)
route=json.loads((p/'gamma-one-analytic-integrality-route-710.json').read_text(encoding='utf-8'))
output('gamma-one-analytic-integrality-audit-route-710.json',json.dumps(route,indent=2)+'\n')
s=(p/'record_gamma_one_fourier_converse_702.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-fourier-converse-2','source-gamma-one-analytic-integrality-3'),('SourceGammaOneFourierConverseAudit2','SourceGammaOneAnalyticIntegralityAudit3'),('SourceGammaOneFourierConverseDependencyAudit2','SourceGammaOneAnalyticIntegralityDependencyAudit3'),('SOURCE GAMMA ONE FOURIER CONVERSE','SOURCE GAMMA ONE ANALYTIC INTEGRALITY'),('gamma-one-fourier-converse-audit-route-702.json','gamma-one-analytic-integrality-audit-route-710.json'),('(2, 2, 10)','(3, 6, 16)'),(' == 2',' == 3'),('all 10 required proof dependencies','all 16 required proof dependencies'),('linterScopes=2','linterScopes=3'),('requiredProofValueEdges=10','requiredProofValueEdges=16'),('modules=2, queries=2','modules=3, queries=6'),('proofEdges=10','proofEdges=16')]:
 assert a in s,a;s=s.replace(a,b)
output('record_gamma_one_analytic_integrality_710.py',s)
print(json.dumps(dict(modules=3,queries=6,edges=16)))