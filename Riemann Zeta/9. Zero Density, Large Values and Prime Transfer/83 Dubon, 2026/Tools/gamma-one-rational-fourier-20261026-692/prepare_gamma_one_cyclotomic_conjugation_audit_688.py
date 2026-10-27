from pathlib import Path
import re,json,hashlib
p=Path(r'E:\Lean\.tmp\dubon83');repo=Path(r'E:\Lean\Riemann Zeta');prod=repo/'9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026/Extension/Dubon2026'
mods=['SourceFrickeCyclotomicConjugateRelation', 'SourceCyclotomicModularLift', 'SourceCyclotomicGammaOneLift', 'SourceCyclotomicLevelRingCovariance', 'SourceCyclotomicConjugateCancellation', 'SourceCyclotomicFractionCovariance', 'SourceCyclotomicConjugateCuspOrder', 'SourceCyclotomicHolomorphicDivision', 'SourceCyclotomicEllipticDivisibility', 'SourceCyclotomicEllipticCoordinates', 'SourceGammaOneCuspCyclotomicConjugation', 'SourceCyclotomicCuspFourierTransport', 'SourceGammaOneCyclotomicFourierConjugation']
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean');s=f.read_text(encoding='utf-8')
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 ns=re.search(r'^namespace (\S+)',s,re.M)[1]+'.'
 for k,n in re.findall(r'^(theorem|def) (\S+)',s,re.M):(ths if k=='theorem' else defs).append(ns+n)
assert (len(ths),len(defs))==(33,2),(len(ths),len(defs))
ns='Dubon2026.SourceFricke.';sf='Dubon2026.SourceFunctionField.'
roots=[ns+'exists_gammaOne_cuspForm_cyclotomic_conjugate']
extra=['Dubon2026.SL2Reduction.SL2_reduction_surjective',ns+'exists_holomorphic_cyclotomic_conjugate',sf+'CuspWeightCriterion.main',ns+'cyclotomicFrickeJShift_ne_zero',ns+'coeffMap_discriminantLaurentK_ringHom',sf+'CuspTaylor.Represents.orderTop',ns+'isZeroAtImInfty_iff_cusp_order_pos',sf+'qExpansion_coeff_width']
required=ths+defs+extra
closure=set(mods);todo=mods.copy()
while todo:
 for imp in re.findall(r'^import (\w+)$',(p/(todo.pop()+'.lean')).read_text(encoding='utf-8'),re.M):
  if (p/(imp+'.lean')).exists() and imp not in closure:closure.add(imp);todo.append(imp)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=[],scratchImportClosure=sorted(closure),separateReason='Every declaration is used by construction of the actual same-weight, same-level Gamma1 cusp form with conjugated width-one Fourier coefficients.')
def output(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-gamma-one-cyclotomic-conjugation-13-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,names in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(names),body)
body=body.replace('SOURCE ORIGINAL PRIMITIVE TATE RESTRICTION','SOURCE GAMMA ONE CYCLOTOMIC CONJUGATION').replace('Original Primitive Tate Restriction','Gamma One Cyclotomic Conjugation')
output('SourceGammaOneCyclotomicConjugationAudit13.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceOriginalPrimitiveTateRestrictionDependencyAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,names in [('roots',roots),('localModules',sorted(closure)),('required',required)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(names),body)
body=body[:body.index('  logInfo m!')]+'''  logInfo m!"SOURCE GAMMA ONE CYCLOTOMIC CONJUGATION DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in actual Gamma1 cusp-form coefficient conjugation. Only declaration values are traversed. Modular covariance, original level invariance, all-cusp vanishing, elliptic divisibility and width-one coefficient compatibility are derived. The source weight balance and original Fricke-image premise are explicit; proved spanning supplies such forms. Rational descent, bounded denominators, differential realization and arithmetic comparison remain; 16/20; DUB-17--20 OPEN."

#eval runPlanarPairingDependencyAudit
'''
output('SourceGammaOneCyclotomicConjugationDependencyAudit13.lean',imports+body)
reuse=[p/(m+'.lean') for m in ['SourceFrickeCyclotomicAnalyticTransport','SourceCuspWeightCriterion','SourceCuspWeightImage','SourceFrickeEllipticCoordinateTwist','SourceFrickeEllipticDivisibilityTwist','SourceCuspWeightImageFourier','SourceGammaOneCyclotomicCuspSpan','SourceCuspFrickeRationalSpan']]
reuse += [prod/'SL2Reduction.lean']
reuse += [p/'gamma1-cusp-realization-reuse-644/P2M/Sol/S_CuspForm_exists_gamma1_qCoeff_eq_algEquiv_apply_of_even.lean.txt']
reuse += [p/'gamma-one-cyclotomic-transport-inputs-reuse-686/P2M/Sol'/q for q in ['S_ModularFunction_exists_mdifferentiable_sigmaTransport_of_frickeQuotient.lean.txt','S_CuspForm_exists_gamma1_frickeRational_sigmaTransport.lean.txt']]
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
route={'scope':688,'chain':'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> actual Gamma1 character realization -> original Picard/H1, full/parabolic, transpose and diamond comparison -> actual differential/cusp comparison -> rational Fourier structure -> actual cyclotomic conjugate cusp forms.','assumptionsToDischarge':'Construct actual integral modular lifts using the already proved SL2 reduction surjectivity, with a direct Gamma1 translation lift preserving the original level. Adjoin induction on original j and Fricke generators transports polynomial fractions and their modular action. The analytic conjugate preserves Laurent order and all-cusp vanishing. Holomorphic division remains in the original cyclotomic fraction algebra, so the actual j and j-1728 power identities transfer both elliptic divisibilities. The already proved cusp characterization constructs an actual same-weight Gamma1 cusp form. Rational Eisenstein and discriminant expansions then transfer the literal width-one Fourier coefficients. None of these analytic, modular, cusp, elliptic or coefficient conclusions remains a premise. The source weight balance and original Fricke-image membership remain explicit; the proved original-image spanning theorem supplies the generating set.','remaining':'Descend the original-image spanning set from cyclotomic coefficients to rational Fourier coefficients using the newly constructed actual conjugates. Prove bounded denominators for the original integral-ratio field, arbitrary cusp differential realization and its converse, actual Hecke comparisons, original finite-character arithmetic realization, all-weight characteristic-zero association, arithmetic automorphy and higher continuation. No unrestricted odd-weight weight-balance claim is made. 16/20; DUB-17--20 OPEN.','shorterRouteReview':'The external coefficient-conjugation proof includes a preliminary descent for every cyclotomic-coefficient form. The existing original Fricke-image generating set already spans the actual cusp space. Construct conjugates only for that necessary generating set, preserving original image membership. Reuse local SL2 reduction, monic analytic reconstruction, cusp characterization, elliptic power identities and Laurent cancellation, avoiding a new rational-at-infinity or recursive coefficient-division framework. Two unused helpers were removed before freezing this scope. Native trace-dual basis results are reserved for the next rational-descent consumer.','externalImport':False,'externalFullClosureVerified':False,'rootPinsChanged':False,'proofLimitsChanged':False}
route.update(reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],modules=mods)
output('gamma-one-cyclotomic-conjugation-route-688.json',json.dumps(route,indent=2)+'\n')
print(json.dumps(dict(modules=len(mods),queries=len(ths+defs),theorems=len(ths),constructions=len(defs),edges=len(required))))
