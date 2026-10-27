from pathlib import Path
import re,json,hashlib
p=Path(r'E:\Lean\.tmp\dubon83');repo=Path(r'E:\Lean\Riemann Zeta');prod=repo/'9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026/Extension/Dubon2026'
mods=['SourceFrickeCyclotomicHolomorphicAlgebra','SourceFrickeScalarExtensionBasis','SourceComplexBasisCoefficientTwist','SourceFrickeCoefficientTwist','SourceFrickeSpanLaurentRealization','SourceLaurentTwistOrder','SourceCuspVanishingOrder','SourceFrickeTwistCuspVanishing']
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean');s=f.read_text(encoding='utf-8')
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 ns=re.search(r'^namespace (\S+)',s,re.M)[1]+'.'
 for k,n in re.findall(r'^(theorem|def) (\S+)',s,re.M):(ths if k=='theorem' else defs).append(ns+n)
assert (len(ths),len(defs))==(23,5),(len(ths),len(defs))
ns='Dubon2026.SourceFricke.';sf='Dubon2026.SourceFunctionField.'
roots=[ns+'frickeCoefficientTwist_isZeroAtImInfty_mul_discriminant_iff']
extra=[ns+'linearIndependent_holomorphic_cyclotomic_fricke_fractions',sf+'CuspTaylor.Represents.cusp_smul_sum',ns+'exists_cyclotomic_fraction_represents',ns+'coeffMap_discriminantLaurentK',ns+'represents_discriminant_width',sf+'CuspTaylor.Represents.order']
required=ths+defs+extra
closure=set(mods);todo=mods.copy()
while todo:
 for imp in re.findall(r'^import (\w+)$',(p/(todo.pop()+'.lean')).read_text(encoding='utf-8'),re.M):
  if (p/(imp+'.lean')).exists() and imp not in closure:closure.add(imp);todo.append(imp)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=[],scratchImportClosure=sorted(closure),separateReason='Every declaration is used by the actual Fricke coefficient-twist cusp-vanishing consumer.')
def output(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-fricke-coefficient-twist-8-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,names in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(names),body)
body=body.replace('SOURCE ORIGINAL PRIMITIVE TATE RESTRICTION','SOURCE FRICKE COEFFICIENT TWIST').replace('Original Primitive Tate Restriction','Fricke Coefficient Twist')
output('SourceFrickeCoefficientTwistAudit8.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceOriginalPrimitiveTateRestrictionDependencyAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,names in [('roots',roots),('localModules',sorted(closure)),('required',required)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(names),body)
body=body[:body.index('  logInfo m!')]+'''  logInfo m!"SOURCE FRICKE COEFFICIENT TWIST DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the actual cusp-vanishing equivalence for a Fricke span function times each discriminant power. Only declaration values are traversed. Actual scalar-extension independence constructs the coefficient twist, literal Laurent expansions prove order preservation, and native meromorphic limits prove cusp-vanishing equivalence. Modular equivariance, elliptic divisibility and cusp-subspace descent remain; 16/20; DUB-17--20 OPEN."

#eval runPlanarPairingDependencyAudit
'''
output('SourceFrickeCoefficientTwistDependencyAudit8.lean',imports+body)
reuse=[p/(m+'.lean') for m in ['SourceFrickeLaurentIndependence','SourceCuspLaurentLinearRelations','SourceMeromorphicCuspPoleClearing','SourceFrickeCyclotomicLaurent']]
reuse += [prod/'SourceCuspDiscRealization.lean']
reuse += [repo/'.lake/packages/mathlib/Mathlib'/q for q in ['LinearAlgebra/Basis/Submodule.lean','LinearAlgebra/Finsupp/Defs.lean','Analysis/Meromorphic/Order.lean','RingTheory/HahnSeries/Basic.lean']]
reuse += [p/'gamma1-rational-structure-input-reuse-646/P2M/Sol/S_CuspForm_span_frickeRational_E4_pow_E6_pow_eq_top.lean.txt']
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
route={'scope':675,'chain':'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> actual Gamma1 character realization -> original Picard/H1, full/parabolic, transpose and diamond comparison -> actual differential/cusp comparison -> rational cusp-form spanning -> coefficient descent of the actual Fricke function span.','assumptionsToDischarge':'Construct the coefficient twist on the actual complex span of original holomorphic cyclotomic Fricke fractions using proved scalar-extension independence, prove its action on every original fraction and every finite complex representation, and prove that twisting preserves the cusp order and cusp vanishing after multiplication by every fixed discriminant power. No continuity of arbitrary complex field automorphisms, twist existence, Fourier threshold criterion or cusp-vanishing preservation is assumed.','remaining':'Modular equivariance and holomorphic divisibility at elliptic points must still be proved; then descend the actual cusp-form image. Arbitrary Gamma1 differential realization and the original finite-character arithmetic association, automorphy and higher continuation chain remain. 16/20; DUB-17--20 OPEN.','shorterRouteReview':'Before expanding the external flatness/twist and q-expansion threshold dependencies, reuse the proved local Laurent independence, native basis and Finsupp coefficient equivalences, existing literal cusp-germ representations, and native meromorphic order/limit theorems. Laurent order is preserved by an injective coefficient map, and the actual discriminant Laurent coefficients lie in the original cyclotomic field. This directly proves cusp-vanishing preservation without a common pole exponent, a separate coefficient-threshold engine or any assertion that the positive-weight discriminant is a weight-zero Fricke fraction. Native basis domains use the original subalgebra.toSubmodule to avoid unnecessary instance diamonds at unchanged limits.','externalImport':False,'externalFullClosureVerified':False,'rootPinsChanged':False,'proofLimitsChanged':False}
route.update(reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],modules=mods)
output('fricke-coefficient-twist-route-675.json',json.dumps(route,indent=2)+'\n')
print(json.dumps(dict(modules=len(mods),queries=len(ths+defs),theorems=len(ths),constructions=len(defs),edges=len(required))))