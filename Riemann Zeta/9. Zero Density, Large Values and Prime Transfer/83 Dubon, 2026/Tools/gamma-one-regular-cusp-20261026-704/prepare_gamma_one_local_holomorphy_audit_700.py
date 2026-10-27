from pathlib import Path
import json,re,hashlib
p=Path(__file__).parent
prod=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
mods=['SourceGammaOneRatioRealization','SourceGammaOneAnalyticGerms','SourceGammaOneMeromorphicRealization','SourceGammaOneRealizationAlgebra','SourceGammaOneAnalyticOrder','SourceGammaOneAnalyticOrderNontrivial','SourceGammaOneAnalyticPlaces','SourceGammaOneJRealization','SourceGammaOneRegularCoefficientOrders','SourceGammaOneAnalyticJOrders','SourceGammaOneAnalyticDifferentialRegularity','SourceGammaOneHolomorphicDifferentials']
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean');assert not (prod/f.name).exists()
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 s=f.read_text(encoding='utf-8');ns=re.search(r'^namespace (\S+)',s,re.M)[1]+'.'
 for k,n in re.findall(r'^(theorem|def) (\S+)',s,re.M):(ths if k=='theorem' else defs).append(ns+n)
assert (len(mods),len(ths),len(defs))==(12,31,4)
sf='Dubon2026.SourceFunctionField.';ns=sf+'GammaOne.'
roots=[ns+'regular_differential_holomorphic_realization']
extra=[ns+'functionFieldOver_modular_ratio',ns+'functionFieldOver_dCoordGenerates',ns+'functionFieldOver_localDifferentials',sf+'jqModC_mul_discriminant_expansion',sf+'meromorphicOrderAt_deriv_jf_add_one','Dubon2026.SourceCurve.Place.exists_place_of_orderMap','Dubon2026.SourceCurve.Place.ordDifferential_D_eq_ord_sub_one',sf+'HolomorphicQuotient.exists_mdifferentiable_mul_eq',sf+'raw_j_derivative_smul',sf+'mdifferentiable_raw_j_derivative',ns+'D_jCoordinateOver_ne_zero']
required=ths+defs+extra;assert len(required)==len(set(required))==46
closure=set(mods);todo=mods.copy()
while todo:
 for imp in re.findall(r'^import (\w+)$',(p/(todo.pop()+'.lean')).read_text(encoding='utf-8'),re.M):
  if (p/(imp+'.lean')).exists() and imp not in closure:closure.add(imp);todo.append(imp)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=[],scratchImportClosure=sorted(closure),separateReason='Every selected declaration advances actual finite-point holomorphic realization of the original regular differential. The unused normalized-place membership wrapper was deferred before auditing.')
def output(n,s):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(s)
output('source-gamma-one-local-holomorphy-12-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8');body=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,values in [('modules',mods),('theorems',ths),('constructions',defs)]:body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(values),body)
body=body.replace('SOURCE ORIGINAL PRIMITIVE TATE RESTRICTION','SOURCE GAMMA ONE LOCAL HOLOMORPHY').replace('Original Primitive Tate Restriction','Gamma One Local Holomorphy')
output('SourceGammaOneLocalHolomorphyAudit12.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceOriginalPrimitiveTateRestrictionDependencyAudit8.lean').read_text(encoding='utf-8');body=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,values in [('roots',roots),('localModules',sorted(closure)),('required',required)]:body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(values),body)
body=body[:body.index('  logInfo m!')]+'  logInfo m!"SOURCE GAMMA ONE LOCAL HOLOMORPHY DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in actual finite-point holomorphic differential realization. Only declaration values are traversed. Actual modular quotient germs supply normalized places. Exact local differential order and the analytic derivative order remove every finite pole. Native removable singularities construct the actual holomorphic weight-two function and its Gamma covariance. All-cusp vanishing, complete Fourier matching, arithmetic comparison and literal higher symmetric-power continuation remain; 16/20; DUB-17--20 OPEN."\n\n#eval runPlanarPairingDependencyAudit\n'
output('SourceGammaOneLocalHolomorphyDependencyAudit12.lean',imports+body)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
f=p/'gamma-one-local-converse-route-700.json';old=json.loads(f.read_text(encoding='utf-8'))
route=dict(scope=700,chain=old['dependency'],modules=mods,assumptionsToDischarge='Every nonzero coefficient x of an actual regular differential x D(j) on the original complex Gamma1 integral-ratio field has a native holomorphic weight-two realization with the exact modular quotient identity and Gamma covariance. No analytic realization, local place, normalization factor, finite-point regularity, local ramification bound or removable-singularity certificate remains assumed. Translation membership and finite index are source group conditions, automatic for Gamma1 at nonzero level.',remaining='All-cusp vanishing and exact differential Fourier matching remain before the complete regular-differential-to-cusp converse. Coefficient-field transport, actual Picard/H1, full/parabolic, transpose and diamond comparison, original finite character arithmetic realization, original all-weight association, local/image/regularity, arithmetic automorphy and literal higher symmetric-power continuation remain. The full goal and all twenty acceptance gates are unchanged; 16/20; DUB-17--20 OPEN.',shorterRouteReview=old['route'],reuseChecked=[dict(path=str(f),sha256=sha(f))]+[dict(path=str(prod/(x['module']+'.lean')),sha256=x['sha256']) for x in old['existingReuse']],externalImport=False,externalFullClosureVerified=False,rootPinsChanged=False,proofLimitsChanged=False)
output('gamma-one-local-holomorphy-audit-route-700.json',json.dumps(route,indent=2)+'\n')
print(json.dumps(dict(modules=12,queries=35,theorems=31,constructions=4,edges=46)))