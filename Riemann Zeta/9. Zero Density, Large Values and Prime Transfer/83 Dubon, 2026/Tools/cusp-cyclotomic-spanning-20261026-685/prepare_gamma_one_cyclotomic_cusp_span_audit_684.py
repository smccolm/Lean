from pathlib import Path
import re,json,hashlib
p=Path(r'E:\Lean\.tmp\dubon83');repo=Path(r'E:\Lean\Riemann Zeta');prod=repo/'9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026/Extension/Dubon2026'
mods=['SourceEisensteinFactorCyclotomicLaurent', 'SourceCuspWeightImageFourier', 'SourceGammaOneCyclotomicCuspSpan']
ths=[];defs=[]
for m in mods:
 f=p/(m+'.lean');s=f.read_text(encoding='utf-8')
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 ns=re.search(r'^namespace (\S+)',s,re.M)[1]+'.'
 for k,n in re.findall(r'^(theorem|def) (\S+)',s,re.M):(ths if k=='theorem' else defs).append(ns+n)
assert (len(ths),len(defs))==(9,1),(len(ths),len(defs))
ns='Dubon2026.SourceFricke.';sf='Dubon2026.SourceFunctionField.'
roots=[ns+'span_gammaOne_weightTwo_cyclotomic_cuspForms_eq_top']
extra=[ns+'span_cuspWeightImage_cyclotomic_fractions_eq_top',ns+'exists_cyclotomic_fraction_represents',sf+'CuspTaylor.Represents.cusp_of_mul_eq',ns+'discriminantLaurentK',ns+'eisensteinQSeries_map',ns+'qExpansion_coeff_width']
required=ths+defs+extra
closure=set(mods);todo=mods.copy()
while todo:
 for imp in re.findall(r'^import (\w+)$',(p/(todo.pop()+'.lean')).read_text(encoding='utf-8'),re.M):
  if (p/(imp+'.lean')).exists() and imp not in closure:closure.add(imp);todo.append(imp)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=[],scratchImportClosure=sorted(closure),separateReason='Every declaration is used by the actual Gamma1 weight-two cusp-form span with original cyclotomic width-one Fourier coefficients.')
def output(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-gamma-one-cyclotomic-cusp-span-3-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,names in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(names),body)
body=body.replace('SOURCE ORIGINAL PRIMITIVE TATE RESTRICTION','SOURCE GAMMA ONE CYCLOTOMIC CUSP SPAN').replace('Original Primitive Tate Restriction','Gamma One Cyclotomic Cusp Span')
output('SourceGammaOneCyclotomicCuspSpanAudit3.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceOriginalPrimitiveTateRestrictionDependencyAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,names in [('roots',roots),('localModules',sorted(closure)),('required',required)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(names),body)
body=body[:body.index('  logInfo m!')]+'''  logInfo m!"SOURCE GAMMA ONE CYCLOTOMIC CUSP SPAN DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the actual Gamma1 weight-two cusp-form span with cyclotomic Fourier coefficients. Only declaration values are traversed. The original Laurent representation and nonzero Eisenstein factor derive the coefficient-field premise, and every periodicity and boundedness premise is discharged for the original Gamma1 cusp forms. Differential realization and arithmetic comparison remain; 16/20; DUB-17--20 OPEN."

#eval runPlanarPairingDependencyAudit
'''
output('SourceGammaOneCyclotomicCuspSpanDependencyAudit3.lean',imports+body)
reuse=[p/(m+'.lean') for m in ['SourceEisensteinRationalSeries','SourceQExpansionLaurentWidth','SourceFrickeCyclotomicFractionGerm','SourceCuspLaurentFractionIdentity','SourceCuspWeightFactors','SourceCuspWeightImage','SourceCuspFrickeRationalSpan']]
reuse += [repo/'.lake/packages/mathlib/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean',prod/'SourceGammaOneRatioClosure.lean']
reuse += [p/'gamma1-rational-structure-input-reuse-646/P2M/Sol/S_ModularForm_gamma1_qExpansion_coeff_mem_of_frickeRational.lean.txt']
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
route={'scope':684,'chain':'DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> actual Gamma1 character realization -> original Picard/H1, full/parabolic, transpose and diamond comparison -> actual differential/cusp comparison -> rational cusp-form spanning.','assumptionsToDischarge':'An original cyclotomic Fricke weight image gives a Laurent representation of the actual cusp form: multiply its Laurent numerator by the actual discriminant power and divide by the nonzero original Eisenstein factor. Uniqueness against the actual q-expansion proves every coefficient lies in the original cyclotomic field. For Gamma1, derive period one, width-N periodicity and cusp boundedness, identify the width-one coefficients, and consume the proved actual Fricke-image span. The actual weight-two Gamma1 cusp space is therefore spanned over the complex numbers by cusp forms with cyclotomic Fourier coefficients.','remaining':'Continue original Gamma1 differential realization and comparison, then finite-character arithmetic realization, original all-weight characteristic-zero association, automorphy and higher continuation. General weight-lowering remains subject to the original balance k+4a+6b=12m; the weight-two specialization uses a=b=m=1 and is unconditional in nonzero level N. No unrestricted odd-weight claim or closure of the arithmetic goal. 16/20; DUB-17--20 OPEN.','shorterRouteReview':'Read the fixed primary Fourier extraction source and checked local rational Eisenstein series, actual Fricke Laurent germs, original weight image, coefficient uniqueness and native width change. The existing Laurent field gives the desired original coefficient-field conclusion directly, avoiding the external recursive power-series unit-division argument and its polynomial-clearing development. Only the Eisenstein-factor Laurent representative and its nonzero germ were missing; both follow from existing native q-expansions and analytic nonvanishing. No external proof is imported.','externalImport':False,'externalFullClosureVerified':False,'rootPinsChanged':False,'proofLimitsChanged':False}
route.update(reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],modules=mods)
output('gamma-one-cyclotomic-cusp-span-route-684.json',json.dumps(route,indent=2)+'\n')
print(json.dumps(dict(modules=len(mods),queries=len(ths+defs),theorems=len(ths),constructions=len(defs),edges=len(required))))
