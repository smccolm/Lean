from pathlib import Path
import re,json,hashlib
p=Path(r'E:\Lean\.tmp\dubon83');repo=Path(r'E:\Lean\Riemann Zeta');prod=repo/'9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026/Extension/Dubon2026'
mods=['SourceCyclotomicTraceStructure', 'SourceGammaOneFourierLinear', 'SourceGammaOneRationalTraceSpan', 'SourceGammaOneRationalCuspSpan']
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean');s=f.read_text(encoding='utf-8')
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 ns=re.search(r'^namespace (\S+)',s,re.M)[1]+'.'
 for k,n in re.findall(r'^(theorem|def) (\S+)',s,re.M):(ths if k=='theorem' else defs).append(ns+n)
assert (len(ths),len(defs))==(8,1),(len(ths),len(defs))
ns='Dubon2026.SourceFricke.';sf='Dubon2026.SourceFunctionField.'
roots=[ns+'span_gammaOne_weightTwo_rational_cuspForms_eq_top']
extra=[ns+'span_cuspWeightImage_cyclotomic_fractions_eq_top',ns+'exists_gammaOne_cuspForm_cyclotomic_conjugate',ns+'gammaOne_cuspWeightImage_qExpansion_coeff_mem','Module.Basis.traceDual_repr_apply','Module.Basis.sum_repr','trace_eq_sum_automorphisms','IsCyclotomicExtension.finiteDimensional','IsCyclotomicExtension.isGalois']
required=ths+defs+extra
closure=set(mods);todo=mods.copy()
while todo:
 for imp in re.findall(r'^import (\w+)$',(p/(todo.pop()+'.lean')).read_text(encoding='utf-8'),re.M):
  if (p/(imp+'.lean')).exists() and imp not in closure:closure.add(imp);todo.append(imp)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=[],scratchImportClosure=sorted(closure),separateReason='Every declaration is used by rational Fourier spanning of the actual weight-two Gamma1 cusp-form space at every nonzero level.')
def output(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-gamma-one-rational-cusp-span-4-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,names in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(names),body)
body=body.replace('SOURCE ORIGINAL PRIMITIVE TATE RESTRICTION','SOURCE GAMMA ONE RATIONAL CUSP SPAN').replace('Original Primitive Tate Restriction','Gamma One Rational Cusp Span')
output('SourceGammaOneRationalCuspSpanAudit4.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceOriginalPrimitiveTateRestrictionDependencyAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,names in [('roots',roots),('localModules',sorted(closure)),('required',required)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(names),body)
body=body[:body.index('  logInfo m!')]+'''  logInfo m!"SOURCE GAMMA ONE RATIONAL CUSP SPAN DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in rational Fourier spanning of the actual weight-two Gamma1 cusp-form space. Only declaration values are traversed. The original Fricke-image spanning set supplies actual cyclotomic conjugates; finite trace sums have rational Fourier coefficients, and the native trace-dual basis reconstructs each generator. Bounded denominators, differential realization and arithmetic comparison remain; 16/20; DUB-17--20 OPEN."

#eval runPlanarPairingDependencyAudit
'''
output('SourceGammaOneRationalCuspSpanDependencyAudit4.lean',imports+body)
reuse=[p/(m+'.lean') for m in ['SourceCuspFrickeRationalSpan','SourceGammaOneCyclotomicCuspSpan','SourceGammaOneCyclotomicFourierConjugation','SourceCuspLaurentFunctionIdentity']]
reuse += [repo/'.lake/packages/mathlib/Mathlib'/q for q in ['RingTheory/Trace/Basic.lean','NumberTheory/Cyclotomic/Basic.lean','NumberTheory/ModularForms/QExpansion.lean']]
reuse += [p/'gamma1-differential-input-reuse-633/P2M/Sol/S_CuspForm_exists_basis_gamma1_qCoeff_mem_range_ratCast.lean.txt']
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
route={'scope':689,'chain':'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> actual Gamma1 character realization -> original Picard/H1, full/parabolic, transpose and diamond comparison -> actual differential/cusp comparison -> rational Fourier spanning.','assumptionsToDischarge':'The actual cyclotomic coefficient field is finite Galois over Q by native cyclotomic-extension theorems. The constructed actual cusp conjugates give trace sums with rational width-one Fourier coefficients. Native trace-dual basis reconstruction expresses each original-image generator as a complex linear combination of those rational forms; Fourier injectivity identifies the original cusp form. The original-image spanning theorem discharges the Fricke-image and conjugation hypotheses in the final full-space spanning consumer. Weight-two rational Fourier spanning holds at every nonzero level. General weight spanning retains the explicit source balance k+4a+6b=12m.','remaining':'Prove bounded denominators for these rational forms in the original integral-ratio field, arbitrary cusp differential realization and its converse, actual Hecke comparisons, original finite-character arithmetic realization, all-weight characteristic-zero association, arithmetic automorphy and higher continuation. No unrestricted odd-weight weight-balance claim is made. 16/20; DUB-17--20 OPEN.','shorterRouteReview':'Read the frozen primary rational-basis proof. Its trace sums are useful, but its Dedekind-independence and matrix-invertibility reconstruction can be replaced by the already proved Mathlib trace-dual basis. The original-image forms already span, so the final consumer needs only conjugation on that generating set and rational spanning, not a new finite-basis selection theorem or conjugation of every cyclotomic-coefficient form. Native Fourier linearity and the local analytic germ identity provide coefficient injectivity. An initial coercion/namespace and broad-simplification failure is preserved; explicit trace identities compile under unchanged limits.','externalImport':False,'externalFullClosureVerified':False,'rootPinsChanged':False,'proofLimitsChanged':False}
route.update(reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],modules=mods)
output('gamma-one-rational-cusp-span-route-689.json',json.dumps(route,indent=2)+'\n')
print(json.dumps(dict(modules=len(mods),queries=len(ths+defs),theorems=len(ths),constructions=len(defs),edges=len(required))))
