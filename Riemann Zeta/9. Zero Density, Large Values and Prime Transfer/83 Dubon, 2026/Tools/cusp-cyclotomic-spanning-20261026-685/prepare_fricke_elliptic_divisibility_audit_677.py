from pathlib import Path
import re,json,hashlib
p=Path(r'E:\Lean\.tmp\dubon83');repo=Path(r'E:\Lean\Riemann Zeta');prod=repo/'9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026/Extension/Dubon2026'
mods=['SourceFrickeHolomorphicDivisionInvariance', 'SourceFrickeHolomorphicDivisionSpan', 'SourceFrickeHolomorphicDivisionTwist', 'SourceFrickeEllipticDivisibilityTwist', 'SourceFrickeEllipticCoordinateTwist']
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean');s=f.read_text(encoding='utf-8')
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 ns=re.search(r'^namespace (\S+)',s,re.M)[1]+'.'
 for k,n in re.findall(r'^(theorem|def) (\S+)',s,re.M):(ths if k=='theorem' else defs).append(ns+n)
assert (len(ths),len(defs))==(9,1),(len(ths),len(defs))
ns='Dubon2026.SourceFricke.';sf='Dubon2026.SourceFunctionField.'
roots=[ns+'frickeCoefficientTwist_E4_divisibility',ns+'frickeCoefficientTwist_E6_divisibility']
extra=[ns+'smul_eq_self_frickeSpan',ns+'smul_mem_frickeSpan',ns+'exists_fricke_twist_laurent',sf+'CuspTaylor.Represents.ne_zero_of_function_ne_zero',sf+'CuspTaylor.Represents.cusp_of_mul_eq',ns+'exists_bounded_mul_discriminant_of_meromorphic',ns+'mem_span_holomorphic_cyclotomic_fractions_of_principal_invariant',ns+'frickeCoefficientTwist_mul',ns+'frickeCoefficientTwist_pow',ns+'frickeCoefficientTwist_fixes_original',sf+'JMultiplicity.jf_surjective',sf+'jf_sub_1728']
required=ths+defs+extra
closure=set(mods);todo=mods.copy()
while todo:
 for imp in re.findall(r'^import (\w+)$',(p/(todo.pop()+'.lean')).read_text(encoding='utf-8'),re.M):
  if (p/(imp+'.lean')).exists() and imp not in closure:closure.add(imp);todo.append(imp)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=[],scratchImportClosure=sorted(closure),separateReason='Every declaration is used by the two actual E4 and E6 divisibility consumers required for cusp-image descent.')
def output(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-fricke-elliptic-divisibility-5-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,names in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(names),body)
body=body.replace('SOURCE ORIGINAL PRIMITIVE TATE RESTRICTION','SOURCE FRICKE ELLIPTIC DIVISIBILITY').replace('Original Primitive Tate Restriction','Fricke Elliptic Divisibility')
output('SourceFrickeEllipticDivisibilityAudit5.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceOriginalPrimitiveTateRestrictionDependencyAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,names in [('roots',roots),('localModules',sorted(closure)),('required',required)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(names),body)
body=body[:body.index('  logInfo m!')]+'''  logInfo m!"SOURCE FRICKE ELLIPTIC DIVISIBILITY DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the actual E4-cube and E6-square divisibility consumers. Only declaration values are traversed. Holomorphic quotient span closure follows from analytic cancellation, literal meromorphic cusp germs, pole clearing and actual function spanning; the coefficient twist then transports the original elliptic identities. Cusp-image characterization and fixed-field descent remain; 16/20; DUB-17--20 OPEN."

#eval runPlanarPairingDependencyAudit
'''
output('SourceFrickeEllipticDivisibilityDependencyAudit5.lean',imports+body)
reuse=[p/(m+'.lean') for m in ['SourceFrickePrincipalInvariance','SourceFrickeTwistPowers','SourceFrickeSpanMultiplication','SourceCuspLaurentFractionIdentity','SourceMeromorphicCuspPoleClearing','SourceFrickeHolomorphicIntegralSpan']]
reuse += [prod/(m+'.lean') for m in ['SourceAnalyticJSurjectivity','SourceInverseJDerivativePower']]
reuse += [p/'gamma1-rational-structure-input-reuse-646/P2M/Sol/S_CuspForm_span_frickeRational_E4_pow_E6_pow_eq_top.lean.txt']
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
route={'scope':677,'chain':'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> actual Gamma1 character realization -> original Picard/H1, full/parabolic, transpose and diamond comparison -> actual differential/cusp comparison -> rational cusp-form spanning -> actual cusp-image stability under coefficient twists.','assumptionsToDischarge':'Prove that a holomorphic quotient of two actual complex Fricke-span functions with nonzero denominator is in the same span: derive principal invariance by analytic cancellation, all translated meromorphic cusp germs by literal Laurent quotients, and finite poles by the existing discriminant pole-clearing theorem. Transport holomorphic division by an original cyclotomic fraction under the actual coefficient twist, then instantiate the exact E4-cube and E6-square divisibility conditions using actual j and j-1728 and their proved identities and nonvanishing.','remaining':'Characterize the actual cusp-form image and perform its fixed-field descent to obtain rational cusp-form spanning. Arbitrary Gamma1 differential realization and the original finite-character arithmetic association, automorphy and higher continuation chain remain. 16/20; DUB-17--20 OPEN.','shorterRouteReview':'The fixed primary source proves special quotient growth using limits of E4 and E6, coordinate invariance and a common finite-pole exponent. Before expanding that argument, check the existing literal Laurent quotient representation, general meromorphic pole clearing and actual function-span consumer. These already show that any holomorphic quotient of two span functions is in the span. This removes the external growth, Eisenstein-limit and full-coordinate-invariance prerequisites from divisibility transport while preserving its source conclusion for all exponents. The unaudited first power-specific invariance attempt is retained in fricke-elliptic-power-route-superseded-677a as a failed route snapshot; the shorter general quotient proof replaces it before any audit. No proof limits or pins change.','externalImport':False,'externalFullClosureVerified':False,'rootPinsChanged':False,'proofLimitsChanged':False}
route.update(reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],modules=mods)
output('fricke-elliptic-divisibility-route-677.json',json.dumps(route,indent=2)+'\n')
print(json.dumps(dict(modules=len(mods),queries=len(ths+defs),theorems=len(ths),constructions=len(defs),edges=len(required))))
