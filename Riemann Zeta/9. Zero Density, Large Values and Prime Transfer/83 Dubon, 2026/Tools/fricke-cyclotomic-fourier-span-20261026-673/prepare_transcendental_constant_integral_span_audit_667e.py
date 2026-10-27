from pathlib import Path
import re,json,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
mods=['SourceTranscendentalConstantAlgebraV2','SourceTranscendentalConstantEvaluationV2','SourceTranscendentalConstantDenominatorsV2','SourceTranscendentalConstantFieldRangeV2','SourceTranscendentalConstantScaledRelationV2','SourceTranscendentalConstantNormalityV2','SourceTranscendentalConstantIntegralSpanV2']
ns='Dubon2026.SourceFricke.ConstantDescent.'
ths=[];defs=[]
propinst={'scalarTowerBaseRationalGenerated','scalarTowerBaseGeneratedAmbient','isDomainCoordinateRing'}
for m in mods:
 f=p/(m+'.lean');s=f.read_text(encoding='utf-8')
 assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 assert f.with_suffix('.olean').stat().st_mtime>=f.stat().st_mtime,m
 for k,n in re.findall(r'^(theorem|abbrev|def|(?:noncomputable )?scoped instance) (\S+)',s,re.M):
  (ths if k=='theorem' or n in propinst else defs).append(ns+n)
assert (len(ths),len(defs))==(23,7),(len(ths),len(defs))
roots=[ns+'mem_span_RSet_of_adjoin_simple_transcendental']
extra=[ns+'isIntegral_subalgebra_iff',ns+'closure_adjoin_le','integralClosure.isDedekindDomain','integralClosure.isFractionRing_of_finite_extension','IntermediateField.finiteDimensional_adjoin','Polynomial.algEquivOfTranscendental','IsFractionRing.div_surjective','IsFractionRing.lift','IsIntegrallyClosed.isIntegral_iff','Polynomial.monic_X_pow_add','IsPrincipalIdealRing.of_surjective']
required=ths+defs+extra
closure=set(mods);todo=mods.copy()
while todo:
 for imp in re.findall(r'^import (\w+)$',(p/(todo.pop()+'.lean')).read_text(encoding='utf-8'),re.M):
  if (p/(imp+'.lean')).exists() and imp not in closure:closure.add(imp);todo.append(imp)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,proofEdges=required,roots=roots,separatelyAxiomChecked=[],scratchImportClosure=sorted(closure),separateReason='All retained declarations serve the transcendental constant-adjoining span theorem; five source aliases absent from its value dependencies were removed before audit.')
def output(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
output('source-transcendental-constant-integral-span-7e-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda names:'#['+', '.join(chr(96)+n for n in names)+']'
imports=''.join('import '+m+'\n' for m in mods)+'import Mathlib.Tactic\n\nopen Lean\n\n'
t=(p/'SourceOriginalPrimitiveTateRestrictionAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingAudit'):t.index('#lint in')]
for k,names in [('modules',mods),('theorems',ths),('constructions',defs)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(names),body)
body=body.replace('SOURCE ORIGINAL PRIMITIVE TATE RESTRICTION','SOURCE TRANSCENDENTAL CONSTANT INTEGRAL SPAN').replace('Original Primitive Tate Restriction','Transcendental Constant Integral Span')
output('SourceTranscendentalConstantIntegralSpanAudit7e.lean',imports+''.join('#print axioms '+n+'\n' for n in cfg['queries'])+'\n'+body+''.join('#lint in '+m+'\n' for m in mods))
t=(p/'SourceOriginalPrimitiveTateRestrictionDependencyAudit8.lean').read_text(encoding='utf-8')
body=t[t.index('private def runPlanarPairingDependencyAudit'):]
for k,names in [('roots',roots),('localModules',sorted(closure)),('required',required)]:
 body=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*',lambda _:'let '+k+' : Array Name := '+arr(names),body)
body=body[:body.index('  logInfo m!')]+'''  logInfo m!"SOURCE TRANSCENDENTAL CONSTANT INTEGRAL SPAN DEPENDENCY AUDIT PASS: all {required.size} required proof dependencies occur in the transcendental constant-adjoining consumer. Only declaration values are traversed. Actual finite integral generators and coordinate transcendence give the normal polynomial coefficient ring; scalar denominators and fraction-field normality give integral coordinates. Relative transcendence, finite constant-list induction, actual Fricke instantiation and rational Fourier spanning remain; 16/20; DUB-17--20 OPEN."

#eval runPlanarPairingDependencyAudit
'''
output('SourceTranscendentalConstantIntegralSpanDependencyAudit7e.lean',imports+body)
route=json.loads((p/'transcendental-constant-integral-span-route-667.json').read_text())
route['modules']=mods
route['shorterRouteReview']+=' The monolithic source argument exceeded the default elaboration limit. The final proof isolates the evaluation field, scalar denominator relation and normality recovery, all under unchanged limits. A read-only value-dependency discovery identified five unused aliases, removed before the final sequential rebuild. The used discovery and pretrim sources, and both failed limit attempts, are retained. All surviving declarations are required by the value audit.'
route['firstAuditFailure']='The original full audit proved the axiom checks but reported two definition-naming linter errors. Original mathematical sources and audit evidence are immutable; fresh V2 modules rename only the two construction identifiers, with identical mathematical statements. No linter is suppressed.'
route['predecessorRouteSha256']=hashlib.sha256((p/'transcendental-constant-integral-span-route-667.json').read_bytes()).hexdigest().upper()
output('transcendental-constant-integral-span-route-667e.json',json.dumps(route,indent=2)+'\n')
print(json.dumps(dict(modules=len(mods),queries=len(ths+defs),theorems=len(ths),constructions=len(defs),edges=len(required))))