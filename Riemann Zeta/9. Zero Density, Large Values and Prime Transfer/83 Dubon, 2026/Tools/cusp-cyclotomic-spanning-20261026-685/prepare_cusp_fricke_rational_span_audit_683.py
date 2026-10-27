from pathlib import Path
import re,json,hashlib
p=Path(r'E:\Lean\.tmp\dubon83');repo=Path(r'E:\Lean\Riemann Zeta');prod=repo/'9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026/Extension/Dubon2026'
mods=['SourcePureTranscendentalConstantIntersection', 'SourceAlgebraicallyClosedFixedField', 'SourceTwistDescentFiniteSupport', 'SourceTwistStableSubspaceDescent', 'SourceOriginalFrickeSpanDescent', 'SourceCuspWeightImageDescent', 'SourceCuspFrickeRationalSpan']
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean');s=f.read_text(encoding='utf-8')
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 ns=re.search(r'^namespace (\S+)',s,re.M)[1]+'.'
 for k,n in re.findall(r'^(theorem|def) (\S+)',s,re.M):(ths if k=='theorem' else defs).append(ns+n)
assert (len(ths),len(defs))==(18,2),(len(ths),len(defs))
ns='Dubon2026.SourceFricke.';sf='Dubon2026.SourceFunctionField.'
roots=[ns+'span_cuspWeightImage_cyclotomic_fractions_eq_top']
extra=[ns+'frickeCoefficientTwist_fixes_original',ns+'frickeCoefficientTwist_smul',ns+'exists_frickeSpan_sum_original',ns+'exists_cuspWeightImage_eq_twist',ns+'cuspWeightImage_injective',ns+'cuspWeightImage_mem_frickeSpan']
required=ths+defs+extra
closure=set(mods);todo=mods.copy()
while todo:
 for imp in re.findall(r'^import (\w+)$',(p/(todo.pop()+'.lean')).read_text(encoding='utf-8'),re.M):
  if (p/(imp+'.lean')).exists() and imp not in closure:closure.add(imp);todo.append(imp)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=[],scratchImportClosure=sorted(closure),separateReason='Every declaration is used by the actual cusp-form spanning consumer after fixed-field descent and injective pullback.')
def output(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-cusp-fricke-rational-span-7-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,names in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(names),body)
body=body.replace('SOURCE ORIGINAL PRIMITIVE TATE RESTRICTION','SOURCE CUSP FRICKE RATIONAL SPAN').replace('Original Primitive Tate Restriction','Cusp Fricke Rational Span')
output('SourceCuspFrickeRationalSpanAudit7.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceOriginalPrimitiveTateRestrictionDependencyAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,names in [('roots',roots),('localModules',sorted(closure)),('required',required)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(names),body)
body=body[:body.index('  logInfo m!')]+'''  logInfo m!"SOURCE CUSP FRICKE RATIONAL SPAN DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the actual cusp-form span of original cyclotomic Fricke weight images. Only declaration values are traversed. Full complex fixed-coefficient descent and finite scalar-support descent are proved, all twist and range-stability premises are derived, and the actual spanning conclusion is pulled back through the original injective map. Cyclotomic Fourier extraction, differential realization and arithmetic comparison remain; 16/20; DUB-17--20 OPEN."

#eval runPlanarPairingDependencyAudit
'''
output('SourceCuspFrickeRationalSpanDependencyAudit7.lean',imports+body)
reuse=[p/(m+'.lean') for m in ['SourceFrickeCoefficientTwist','SourceFrickeTwistModularEquivariance','SourceCuspWeightImage','SourceCuspWeightImageSpan','SourceCuspWeightImageTwist']]
reuse += [repo/'.lake/packages/mathlib/Mathlib/LinearAlgebra/Span/Basic.lean',repo/'.lake/packages/mathlib/Mathlib/FieldTheory/Galois/Infinite.lean']
reuse += [p/'fricke-cusp-descent-inputs-reuse-678/P2M/Sol'/q for q in ['S_WLight_span_inter_rational_of_twist_stable.lean.txt','S_IsAlgClosed_exists_algEquiv_apply_ne_of_notMem_range.lean.txt']]
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
route={'scope':683,'chain':'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> actual Gamma1 character realization -> original Picard/H1, full/parabolic, transpose and diamond comparison -> actual differential/cusp comparison -> rational cusp-form spanning.','assumptionsToDischarge':'Prove the original characteristic-zero field is the full fixed field of the algebraically closed ambient-field automorphisms, treating both algebraic and transcendental coefficients. Prove finite-support descent of a twist-stable subspace, then derive every premise for the actual cusp-image range using the already proved original Fricke span, coefficient twist and same-weight cusp-image realization. Pull the resulting span back through the actual injective weight-lowering map: the actual cusp-form space is spanned by forms whose weight-lowered images are holomorphic fractions over the original cyclotomic Fricke ring.','remaining':'Extract cyclotomic Fourier coefficients of the original cusp forms from these actual Fricke representations, then continue arbitrary Gamma1 differential realization and the original finite-character arithmetic association, automorphy and higher continuation chain. The source balance k+4a+6b=12m remains explicit; the required geometric weight-two application has a=b=m=1. This does not assert an unrestricted odd-weight weight-lowering representation or close the all-weight arithmetic goal. 16/20; DUB-17--20 OPEN.','shorterRouteReview':'Local and pinned-native searches found no ready theorem for the full algebraically closed fixed field or twist-stable subspace descent. Adapt only the two necessary abstract primary arguments. Native fraction-ring integrality, minpoly roots, transcendence bases and InfiniteGalois.mem_bot_iff_fixed prove coefficient separation; finite scalar-support induction and finite-dimensional complements prove stable-subspace descent. The actual local basis coefficient twist eliminates the separate external flatness/twist construction and specialized function wrapper. Work in the original complex Fricke span itself, avoiding a total extension of the twist to arbitrary functions. Native LinearMap.apply_mem_span_image_iff_mem_span pulls the span back through the proved original injective map.','externalImport':False,'externalFullClosureVerified':False,'rootPinsChanged':False,'proofLimitsChanged':False}
route.update(reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],modules=mods)
output('cusp-fricke-rational-span-route-683.json',json.dumps(route,indent=2)+'\n')
print(json.dumps(dict(modules=len(mods),queries=len(ths+defs),theorems=len(ths),constructions=len(defs),edges=len(required))))
