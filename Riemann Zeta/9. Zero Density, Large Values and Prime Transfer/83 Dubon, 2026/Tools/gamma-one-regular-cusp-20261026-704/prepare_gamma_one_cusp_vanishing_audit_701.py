from pathlib import Path
import json,re,hashlib
p=Path(__file__).parent
prod=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
mods=['SourceGammaOneTranslatedCuspGerms','SourceGammaOneCuspRatioRealization','SourceGammaOneCuspRealizationAlgebra','SourceGammaOneCuspOrder','SourceGammaOneCuspJOrder','SourceGammaOneCuspPlaces','SourceGammaOneCuspDerivativeOrder','SourceGammaOneDifferentialCuspGerm','SourceGammaOneRegularCuspOrder','SourceGammaOneRegularCuspForms']
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean');assert not (prod/f.name).exists()
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 s=f.read_text(encoding='utf-8');ns=re.search(r'^namespace (\S+)',s,re.M)[1]+'.'
 for k,n in re.findall(r'^(theorem|def) (\S+)',s,re.M):(ths if k=='theorem' else defs).append(ns+n)
assert (len(mods),len(ths),len(defs))==(10,32,4),(len(mods),len(ths),len(defs))
sf='Dubon2026.SourceFunctionField.';ns=sf+'GammaOne.'
roots=[ns+'regular_differential_cusp_form_realization']
extra=[ns+'exists_holomorphic_differential',ns+'regular_coefficient_order_bound',ns+'realize_jCoordinateOver',ns+'functionFieldOver_modular_ratio',sf+'exists_raw_j_derivative_formula',sf+'raw_j_derivative_smul','Dubon2026.SourceFricke.isZeroAtImInfty_iff_cusp_order_pos','Dubon2026.SourceCurve.Place.exists_place_of_orderMap','Dubon2026.SourceCurve.Place.ordDifferential_D_eq_ord_sub_one',ns+'CuspAuxiliary.natCast_mem_strictPeriods_conj']
required=ths+defs+extra;assert len(required)==len(set(required))==46
closure=set(mods);todo=mods.copy()
while todo:
 for imp in re.findall(r'^import (\w+)$',(p/(todo.pop()+'.lean')).read_text(encoding='utf-8'),re.M):
  if (p/(imp+'.lean')).exists() and imp not in closure:closure.add(imp);todo.append(imp)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=[],scratchImportClosure=sorted(closure),separateReason='All selected declarations advance actual all-cusp vanishing and the native cusp-form realization of original regular differentials.')
def output(n,s):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(s)
output('source-gamma-one-cusp-vanishing-10-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceGammaOneLocalHolomorphyAudit12.lean').read_text(encoding='utf-8');body=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,values in [('modules',mods),('theorems',ths),('constructions',defs)]:body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(values),body)
body=body.replace('SOURCE GAMMA ONE LOCAL HOLOMORPHY','SOURCE GAMMA ONE CUSP VANISHING').replace('Gamma One Local Holomorphy','Gamma One Cusp Vanishing')
output('SourceGammaOneCuspVanishingAudit10.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceGammaOneLocalHolomorphyDependencyAudit12.lean').read_text(encoding='utf-8');body=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,values in [('roots',roots),('localModules',sorted(closure)),('required',required)]:body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(values),body)
body=body[:body.index('  logInfo m!')]+'  logInfo m!"SOURCE GAMMA ONE CUSP VANISHING DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in actual regular-differential cusp-form realization. Only declaration values are traversed. Translated modular quotient germs define actual normalized cusp places. The pole of j and exact derivative order turn regularity into positive cusp order. Existing finite holomorphy and all-cusp vanishing construct the native weight-two cusp form. Exact Fourier normalization, coefficient transport, Hecke/diamond arithmetic comparison and literal higher symmetric-power continuation remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOneCuspVanishingDependencyAudit10.lean',imports+body)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
f=p/'gamma-one-cusp-vanishing-route-701.json';old=json.loads(f.read_text(encoding='utf-8'))
route=dict(chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> actual finite Gamma1 Hecke-character realization -> actual Picard/H1 and full/parabolic transpose/diamond comparison retaining the original homogeneous coefficient endomorphism -> actual differential/cusp comparison -> native cusp-form realization of regular differentials.',assumptionsToDischarge=['Actual translated modular quotient germs are meromorphic and define a nontrivial normalized place.','The actual j coordinate and its literal analytic derivative have the same negative cusp order.','Original regularity implies positive cusp order of the holomorphic slash realization at every cusp.','Finite holomorphy and all-cusp vanishing construct an actual native cusp form without supplied decay or cusp-form witnesses.'],remaining='Exact Fourier normalization, coefficient-field transport, complete differential/cusp equivalence, original Hecke/diamond/Picard/H1 arithmetic comparison, all-weight characteristic-zero association and literal higher symmetric-power continuation remain. 16/20; DUB-17--20 OPEN.',reuseChecked=[dict(path=str(z),sha256=sha(z)) for z in [p/'SourceGammaOneHolomorphicDifferentials.lean',p/'SourceGammaOneRegularCoefficientOrders.lean',prod/'SourceCurveOrderMapPlaces.lean',prod/'SourceInverseJDerivativePower.lean',prod/'SourceCuspVanishingOrder.lean',prod/'SourceOriginalRegularCuspForms.lean']],initialRoute=dict(path=str(f),sha256=sha(f),review=old),shorterRoute='Normalize actual cusp orders directly; no global cusp-width classification, Gamma1 ramification classification or auxiliary degree bound.',rootPinsChanged=False,proofLimitsChanged=False)
output('gamma-one-cusp-vanishing-audit-route-701.json',json.dumps(route,indent=2)+'\n')
s=(p/'record_gamma_one_local_holomorphy_700.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-local-holomorphy-12','source-gamma-one-cusp-vanishing-10'),('SourceGammaOneLocalHolomorphyAudit12','SourceGammaOneCuspVanishingAudit10'),('SourceGammaOneLocalHolomorphyDependencyAudit12','SourceGammaOneCuspVanishingDependencyAudit10'),('SOURCE GAMMA ONE LOCAL HOLOMORPHY','SOURCE GAMMA ONE CUSP VANISHING'),('gamma-one-local-holomorphy-audit-route-700.json','gamma-one-cusp-vanishing-audit-route-701.json'),('(12, 35, 46)','(10, 36, 46)'),(' == 12',' == 10'),('linterScopes=12','linterScopes=10'),('modules=12, queries=35','modules=10, queries=36')]:
 assert a in s,a;s=s.replace(a,b)
output('record_gamma_one_cusp_vanishing_701.py',s)
print(json.dumps(dict(modules=10,theorems=32,constructions=4,queries=36,edges=46)))