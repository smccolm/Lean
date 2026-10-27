from pathlib import Path
import re,json,hashlib
p=Path(r'E:\Lean\.tmp\dubon83');repo=Path(r'E:\Lean\Riemann Zeta');prod=repo/'9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026/Extension/Dubon2026'
mods=['SourceCyclotomicFrickeIndex', 'SourceFrickeLaurentCyclotomicConjugation', 'SourceFrickeLaurentFieldConjugation', 'SourceOriginalFrickeLaurentField', 'SourceFrickeCyclotomicAnalyticTransport']
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean');s=f.read_text(encoding='utf-8')
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 ns=re.search(r'^namespace (\S+)',s,re.M)[1]+'.'
 for k,n in re.findall(r'^(theorem|def) (\S+)',s,re.M):(ths if k=='theorem' else defs).append(ns+n)
assert (len(ths),len(defs))==(17,2),(len(ths),len(defs))
ns='Dubon2026.SourceFricke.';sf='Dubon2026.SourceFunctionField.'
roots=[ns+'exists_holomorphic_cyclotomic_conjugate']
extra=[ns+'frickeHQSeriesK_map_cyclotomic',ns+'isPrimitiveRoot_zetaN',ns+'coeffMap_discriminantLaurentK',ns+'exists_holomorphic_cyclotomic_fraction_of_integral_laurent',ns+'exists_fraction_and_monic_j_of_principal_invariant',ns+'exists_bounded_mul_discriminant_of_meromorphic',sf+'isIntegral_adjoin_coeffMap_of_isIntegral',sf+'isIntegral_adjoin_of_isIntegral_coeffMap']
required=ths+defs+extra
closure=set(mods);todo=mods.copy()
while todo:
 for imp in re.findall(r'^import (\w+)$',(p/(todo.pop()+'.lean')).read_text(encoding='utf-8'),re.M):
  if (p/(imp+'.lean')).exists() and imp not in closure:closure.add(imp);todo.append(imp)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=[],scratchImportClosure=sorted(closure),separateReason='Every declaration is used by analytic realization of the conjugated original cyclotomic Fricke Laurent germ.')
def output(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-fricke-cyclotomic-analytic-transport-5-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,names in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(names),body)
body=body.replace('SOURCE ORIGINAL PRIMITIVE TATE RESTRICTION','SOURCE FRICKE CYCLOTOMIC ANALYTIC TRANSPORT').replace('Original Primitive Tate Restriction','Fricke Cyclotomic Analytic Transport')
output('SourceFrickeCyclotomicAnalyticTransportAudit5.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceOriginalPrimitiveTateRestrictionDependencyAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,names in [('roots',roots),('localModules',sorted(closure)),('required',required)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(names),body)
body=body[:body.index('  logInfo m!')]+'''  logInfo m!"SOURCE FRICKE CYCLOTOMIC ANALYTIC TRANSPORT DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in actual holomorphic Fricke conjugation. Only declaration values are traversed. The original Laurent field and its j-integrality are preserved, every membership and integrality premise is derived from the actual original fraction, and the existing holomorphic representative theorem constructs an actual conjugate function. Modular and cusp compatibility, rational cusp descent and arithmetic comparison remain; 16/20; DUB-17--20 OPEN."

#eval runPlanarPairingDependencyAudit
'''
output('SourceFrickeCyclotomicAnalyticTransportDependencyAudit5.lean',imports+body)
reuse=[p/(m+'.lean') for m in ['SourceFrickeProductCyclotomic','SourceFrickeCyclotomicLaurent','SourceFrickePrincipalInvariance','SourceFrickeModularOrbitV2','SourceFrickeIntegralHolomorphicRepresentative','SourceLaurentIntegralCoefficientImage']]
reuse += [repo/'.lake/packages/mathlib/Mathlib/RingTheory/RootsOfUnity/PrimitiveRoots.lean',repo/'.lake/packages/mathlib/Mathlib/RingTheory/IntegralClosure/IsIntegral/Basic.lean']
reuse += [p/'gamma1-cusp-realization-reuse-644/P2M/Sol/S_CuspForm_exists_gamma1_qCoeff_eq_algEquiv_apply_of_even.lean.txt']
reuse += [p/'gamma-one-cyclotomic-transport-inputs-reuse-686/P2M/Sol'/q for q in ['S_ModularFunction_exists_mdifferentiable_sigmaTransport_of_frickeQuotient.lean.txt','S_CuspForm_exists_gamma1_frickeRational_sigmaTransport.lean.txt']]
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
route={'scope':687,'chain':'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> actual Gamma1 character realization -> original Picard/H1, full/parabolic, transpose and diamond comparison -> actual differential/cusp comparison -> rational Fourier structure -> cyclotomic coefficient conjugation.','assumptionsToDischarge':'The actual primitive cyclotomic root determines the unit torsion-index permutation. The proved torsion Fourier formula identifies coefficient conjugation on each literal Laurent generator. Native adjoin induction and integral-equation transport preserve the original generated field and j-integrality. An actual holomorphic original Fricke fraction has a Laurent germ in that field; principal invariance, all modular cusp bounds and its monic relation are derived, yielding integrality without an assumed equation. The existing holomorphic Fricke representative theorem then constructs the actual function realizing the conjugated Laurent germ.','remaining':'Prove modular covariance, elliptic divisibility and cusp compatibility for this nontrivial cyclotomic conjugation, then construct the conjugated original Gamma1 cusp form. Descend the cyclotomic span to Q, prove the needed bounded denominators for the original integral-ratio field, realize arbitrary cusp differentials and their converse, and continue original finite-character arithmetic realization, all-weight characteristic-zero association, automorphy and higher continuation. No cusp-conjugation or rational-spanning gate is claimed closed here. 16/20; DUB-17--20 OPEN.','shorterRouteReview':'Read the primary actual quotient-transport construction and Gamma1/modular conjugation subsections at the frozen commit. The external proof transports cleared polynomial relations and reconstructs holomorphic quotients. The local integral-Laurent representative theorem already performs that analytic reconstruction. Preserve the original Laurent generated field and monic integrality directly under the proved coefficient permutation and reuse that theorem. This avoids importing the external rational-at-infinity package, recursive Fourier division and repeated monic removable-singularity development. Native roots-of-unity automorphism exponents and integral-map transport discharge the two algebraic inputs.','externalImport':False,'externalFullClosureVerified':False,'rootPinsChanged':False,'proofLimitsChanged':False}
route.update(reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],modules=mods)
output('fricke-cyclotomic-analytic-transport-route-687.json',json.dumps(route,indent=2)+'\n')
print(json.dumps(dict(modules=len(mods),queries=len(ths+defs),theorems=len(ths),constructions=len(defs),edges=len(required))))
