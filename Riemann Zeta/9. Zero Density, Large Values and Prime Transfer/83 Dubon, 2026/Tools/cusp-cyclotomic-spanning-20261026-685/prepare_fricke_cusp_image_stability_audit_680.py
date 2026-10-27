from pathlib import Path
import re,json,hashlib
p=Path(r'E:\Lean\.tmp\dubon83');repo=Path(r'E:\Lean\Riemann Zeta');prod=repo/'9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026/Extension/Dubon2026'
mods=['SourceHolomorphicCoprimeDivision', 'SourceCuspWeightFactors', 'SourceCuspWeightHolomorphicDivision', 'SourceCuspWeightTransformation', 'SourceCuspWeightCriterion', 'SourceCuspWeightImage', 'SourceFrickeTwistCuspConditions', 'SourceCuspWeightImageSpan', 'SourceCuspWeightImageTwist']
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean');s=f.read_text(encoding='utf-8')
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 ns=re.search(r'^namespace (\S+)',s,re.M)[1]+'.'
 for k,n in re.findall(r'^(theorem|def) (\S+)',s,re.M):(ths if k=='theorem' else defs).append(ns+n)
assert (len(ths),len(defs))==(24,3),(len(ths),len(defs))
ns='Dubon2026.SourceFricke.';sf='Dubon2026.SourceFunctionField.'
roots=[ns+'exists_cuspWeightImage_eq_twist',ns+'cuspWeightImage_injective']
extra=[sf+'exists_mdifferentiable_quotient_of_monic',sf+'JMultiplicity.E₄_smul',sf+'JMultiplicity.E₆_smul',sf+'JMultiplicity.Δ_smul',sf+'JMultiplicity.tendsto_E₄_atImInfty',ns+'mem_span_holomorphic_cyclotomic_fractions_of_principal_invariant',ns+'frickeCoefficientTwist_E4_divisibility',ns+'frickeCoefficientTwist_E6_divisibility',ns+'frickeCoefficientTwist_pullback',ns+'frickeCoefficientTwist_isZeroAtImInfty_sl_mul_discriminant_iff']
required=ths+defs+extra
closure=set(mods);todo=mods.copy()
while todo:
 for imp in re.findall(r'^import (\w+)$',(p/(todo.pop()+'.lean')).read_text(encoding='utf-8'),re.M):
  if (p/(imp+'.lean')).exists() and imp not in closure:closure.add(imp);todo.append(imp)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=[],scratchImportClosure=sorted(closure),separateReason='Every declaration is used by the actual cusp-image twist-stability or original-image injectivity consumer required for fixed-field descent.')
def output(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-fricke-cusp-image-stability-9-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,names in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(names),body)
body=body.replace('SOURCE ORIGINAL PRIMITIVE TATE RESTRICTION','SOURCE FRICKE CUSP IMAGE STABILITY').replace('Original Primitive Tate Restriction','Fricke Cusp Image Stability')
output('SourceFrickeCuspImageStabilityAudit9.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceOriginalPrimitiveTateRestrictionDependencyAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,names in [('roots',roots),('localModules',sorted(closure)),('required',required)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(names),body)
body=body[:body.index('  logInfo m!')]+'''  logInfo m!"SOURCE FRICKE CUSP IMAGE STABILITY DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in actual cusp-image twist stability and injectivity. Only declaration values are traversed. Local monic division and native analytic gluing prove the exact cusp-image criterion; all elliptic, cusp and subgroup conditions are derived for the twisted original image, producing an actual cusp form of the same weight and subgroup. Fixed-field descent and rational cusp spanning remain; 16/20; DUB-17--20 OPEN."

#eval runPlanarPairingDependencyAudit
'''
output('SourceFrickeCuspImageStabilityDependencyAudit9.lean',imports+body)
reuse=[p/(m+'.lean') for m in ['SourceHolomorphicMonicQuotient','SourceFrickeEllipticCoordinateTwist','SourceFrickeTwistModularEquivariance','SourceFrickeHolomorphicIntegralSpan']]
reuse += [prod/(m+'.lean') for m in ['SourceAnalyticJTransformation','SourceInverseJLimits']]
reuse += [repo/'.lake/packages/mathlib/Mathlib/Geometry/Manifold/MFDeriv/Basic.lean',p/'fricke-cusp-descent-inputs-reuse-678/P2M/Sol/S_CuspForm_exists_mul_E4_pow_mul_E6_pow_eq_iff.lean.txt',p/'gamma1-rational-structure-input-reuse-646/P2M/Sol/S_CuspForm_span_frickeRational_E4_pow_E6_pow_eq_top.lean.txt']
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
route={'scope':680,'chain':'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> actual Gamma1 character realization -> original Picard/H1, full/parabolic, transpose and diamond comparison -> actual differential/cusp comparison -> rational cusp-form spanning -> actual cusp-image stability under coefficient twists.','assumptionsToDischarge':'Prove the exact weight-lowering criterion for actual cusp forms of every integer weight and finite-index subgroup with k+4a+6b=12m. Construct the holomorphic quotient by the original E4/E6 factor from the two power-divisibility conditions using local monic division and coprime analytic gluing; derive its slash invariance and cusp vanishing. Prove the original weight-lowering map is holomorphic and injective. For every subgroup containing Gamma(N), derive actual Fricke-span membership and all conditions of the twisted image, then construct an actual cusp form of the same weight and subgroup realizing that twist.','remaining':'Descend the proved twist-stable cusp image by the original cyclotomic fixed field and pull back the spanning statement through the injective original map. Arbitrary Gamma1 differential realization and the original finite-character arithmetic association, automorphy and higher continuation chain remain. 16/20; DUB-17--20 OPEN.','shorterRouteReview':'The newly checked fixed primary cusp-image file imports a monic quotient theorem already proved locally. Reuse it, native manifold-local congruence for coprime gluing, native analytic-domain cancellation, and the existing E4/E6/discriminant transformation laws and E4 cusp limit. Only the missing E6 limit is proved from its native constant Fourier coefficient. The original cusp image consumes the exact criterion and the actual function-span theorem. Already proved elliptic transport, all-cusps vanishing and modular equivariance discharge the twist stability conditions, so no image-stability premise or externally assumed cusp form is used. The failed transformation preparer and its missing-file diagnostic are preserved under cusp-weight-transformation-preparer-failed-679a, with fresh preparer 679b.','externalImport':False,'externalFullClosureVerified':False,'rootPinsChanged':False,'proofLimitsChanged':False}
route.update(reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],modules=mods)
output('fricke-cusp-image-stability-route-680.json',json.dumps(route,indent=2)+'\n')
print(json.dumps(dict(modules=len(mods),queries=len(ths+defs),theorems=len(ths),constructions=len(defs),edges=len(required))))
