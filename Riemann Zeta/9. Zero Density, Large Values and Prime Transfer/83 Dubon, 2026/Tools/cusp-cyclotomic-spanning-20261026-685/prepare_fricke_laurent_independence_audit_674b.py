from pathlib import Path
import re,json,hashlib
p=Path(r'E:\Lean\.tmp\dubon83');repo=Path(r'E:\Lean\Riemann Zeta');prod=repo/'9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026/Extension/Dubon2026'
mods=['SourceCuspLaurentLinearRelations','SourceFrickeLaurentIndependence']
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean');s=f.read_text(encoding='utf-8')
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 ns=re.search(r'^namespace (\S+)',s,re.M)[1]+'.'
 for k,n in re.findall(r'^(theorem|def) (\S+)',s,re.M):(ths if k=='theorem' else defs).append(ns+n)
assert (len(ths),len(defs))==(5,0),(len(ths),len(defs))
ns='Dubon2026.SourceFricke.';sf='Dubon2026.SourceFunctionField.'
roots=[ns+'linearIndependent_holomorphic_cyclotomic_fricke_fractions']
extra=[sf+'linearIndependent_coeffMap_algebraMap',ns+'exists_cyclotomic_fraction_represents',ns+'holomorphicCyclotomicFrickeFractions_periodic',sf+'CuspTaylor.Represents.eq_upperHalfPlane',sf+'CuspTaylor.Represents.eq_series']
required=ths+defs+extra
closure=set(mods);todo=mods.copy()
while todo:
 for imp in re.findall(r'^import (\w+)$',(p/(todo.pop()+'.lean')).read_text(encoding='utf-8'),re.M):
  if (p/(imp+'.lean')).exists() and imp not in closure:closure.add(imp);todo.append(imp)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=[],scratchImportClosure=sorted(closure),separateReason='Every declaration is used in the actual cyclotomic Fricke independence consumer required for coefficient descent.')
def output(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-fricke-laurent-independence-2-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,names in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(names),body)
body=body.replace('SOURCE ORIGINAL PRIMITIVE TATE RESTRICTION','SOURCE FRICKE LAURENT INDEPENDENCE').replace('Original Primitive Tate Restriction','Fricke Laurent Independence')
output('SourceFrickeLaurentIndependenceAudit2.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceOriginalPrimitiveTateRestrictionDependencyAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,names in [('roots',roots),('localModules',sorted(closure)),('required',required)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(names),body)
body=body[:body.index('  logInfo m!')]+'''  logInfo m!"SOURCE FRICKE LAURENT INDEPENDENCE DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the actual Fricke independence consumer. Only declaration values are traversed. Literal cusp-germ representations transport finite linear relations, and the existing coefficient-map independence theorem proves independence over the complex numbers. Coefficient twists, cusp-subspace descent and arithmetic comparison remain; 16/20; DUB-17--20 OPEN."

#eval runPlanarPairingDependencyAudit
'''
output('SourceFrickeLaurentIndependenceDependencyAudit2.lean',imports+body)
reuse=[p/(m+'.lean') for m in ['SourceFrickeHolomorphicIntegralSpan','SourceFrickeCyclotomicFractionGerm','SourceCuspLaurentSpan','SourceCuspLaurentPolynomial']]
reuse += [prod/(m+'.lean') for m in ['SourceLaurentScalarIndependence','SourceGammaOneRationalRelation']]
reuse += [p/'gamma1-rational-structure-input-reuse-646/P2M/Sol/S_CuspForm_span_frickeRational_E4_pow_E6_pow_eq_top.lean.txt']
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
route={'scope': 674, 'chain': 'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> actual Gamma1 character realization -> original Picard/H1, full/parabolic, transpose and diamond comparison -> actual differential/cusp comparison -> rational cusp-form spanning -> coefficient descent of the actual Fricke function span.', 'assumptionsToDischarge': 'For a family of actual holomorphic cyclotomic Fricke fractions, prove that linear independence over the original cyclotomic field implies complex linear independence. Literal finite linear relations are transported through the proved cusp-germ representation; no scalar-extension independence or common clearing exponent is assumed.', 'remaining': 'Coefficient twists and descent of the actual cusp-form subspace remain, including preservation of modular weight, holomorphy at elliptic points and cusp vanishing. Then arbitrary Gamma1 differential realization and the original finite-character arithmetic association, automorphy and higher continuation chain remain. 16/20; DUB-17--20 OPEN.', 'shorterRouteReview': 'Read the fixed primary Fricke cusp-spanning source and check local SourceGammaOneRationalRelation and SourceLaurentScalarIndependence before expanding its separate q-expansion independence theorem. The local coefficient-map theorem already proves scalar-extension independence for arbitrary Laurent series. Exact finite-sum cusp representations transfer the statement to actual Fricke functions directly, avoiding a separate common-pole Fourier argument. Index types are the ordinary Type used by actual function and basis families and the native finite-sum differentiability theorem.', 'externalImport': False, 'externalFullClosureVerified': False, 'rootPinsChanged': False, 'proofLimitsChanged': False}
route.update(reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],modules=mods)
output('fricke-laurent-independence-route-674.json',json.dumps(route,indent=2)+'\n')
print(json.dumps(dict(modules=len(mods),queries=len(ths+defs),theorems=len(ths),constructions=len(defs),edges=len(required))))