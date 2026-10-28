from pathlib import Path
from datetime import datetime,timezone
import json,re,hashlib
p=Path(__file__).parent
names=[('SourceCocycleConjugateCoboundary','1151a'),('SourceParabolicFiniteCuspWitnesses','1152a'),('SourceParabolicWitnessDenominators','1153a'),('SourceParabolicUniformDenominator','1154a'),('SourceOriginalBinaryCuspWitnesses','1155a'),('SourceParabolicIntegralCoordinateSpan','1156b'),('SourceOriginalIntegralParabolicCocycleSpan','1157a'),('SourceOriginalIntegralParabolicH1Span','1158b')]
mods=[n for n,a in names];ths=[];defs=[]
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
for n,a in names:
 t=(p/(n+'.lean')).read_text(encoding='utf-8');t=re.sub(r'/\-.*?\-/','',t,flags=re.S);t=re.sub(r'--[^\n]*','',t)
 ns=re.search(r'^namespace (\S+)',t,re.M)[1]+'.'
 ths += [ns+x for x in re.findall(r'^theorem (\w+)',t,re.M)]
 defs += [ns+x for x in re.findall(r'^(?:def|abbrev) (\w+)',t,re.M)]
 assert (p/(n+a+'.exit')).read_text().strip()=='0' and (p/(n+a+'.log')).stat().st_size==0,n
roots=['Dubon2026.sourcePrimitive_originalIntegralParabolic_span','Dubon2026.sourceOriginalBinaryPeriodCocycleCoordinate_cusp_witnesses']
edges=ths+defs+['Dubon2026.'+x for x in ['sourcePeriodCocycle_parabolic','sourceRationalBinaryCocycle_integerMultiple','sourceBinaryCoefficientMap_equivariant','sourceParabolic_exists_fixed_cusp','sourceBinaryH1Change_cocycle','sourceParabolicH1_cocycle_iff','sourcePrimitive_binaryPeriodCohomology_ne_zero','sourceHomogeneousAdditiveMap_matrix']]
prior=json.loads((p/'source-parabolic-rational-span-1-audit-config.json').read_text())
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,roots=roots,proofEdges=edges,localModules=list(dict.fromkeys(mods+prior['localModules'])),separatelyAxiomChecked=[],compileEvidence={n:n+a for n,a in names})
def write(n,t):
 f=p/n;assert not f.exists(),f;f.write_text(t,encoding='utf-8')
stem='source-original-integral-parabolic-1'
write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
imports='\n'.join('import '+n for n in mods)+'\nimport Mathlib.Tactic\n'
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
old='SourceParabolicRationalSpan';new='SourceOriginalIntegralParabolic'
for suffix,newSuffix in [('Audit1','Audit1'),('DependencyAudit1','DependencyAudit1'),('ScratchOwnership1150','ScratchOwnership1161')]:
 t=(p/(old+suffix+'.lean')).read_text(encoding='utf-8');t=imports+t[t.index('\nopen Lean'):]
 if suffix=='Audit1':
  t=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in ths+defs),t,count=1)
  for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:t=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),t)
  t=re.sub(r'#lint in [^\n]+\n','',t).rstrip()+'\n\n'+'\n'.join('#lint in '+m for m in mods)+'\n'
 elif suffix=='DependencyAudit1':
  for k,v in [('roots',roots),('localModules',cfg['localModules']),('required',edges)]:t=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),t)
  t=t.replace('actual original primitive period-class rational parabolic span VALUE closure. Rational coordinates preserve actual local coboundaries. Uniform integral parabolic denominator clearing, integral spanning, finite character descent, diamonds and Galois realization remain','actual original primitive period-class integral parabolic span VALUE closure. Whole-cusp witnesses are retained under original coefficient conversion and rational projection; one uniform denominator clears the cocycle and all finite cusp representatives. Finite character descent, diamonds and Galois realization remain')
 else:t=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),t)
 t=t.replace('PARABOLIC RATIONAL SPAN','ORIGINAL INTEGRAL PARABOLIC').replace('Parabolic Rational Span','Original Integral Parabolic')
 write(new+newSuffix+'.lean',t)
rf=p/'source-parabolic-integral-denominator-reuse-1151.json';route=json.loads(rf.read_text())
route['reuseChecked'].append(dict(path=str(rf),sha256=sha(rf)))
route['assumptionsToDischarge']=['Native cocycle conjugation transports actual local coboundary witnesses.','Finitely many original cusp-orbit representatives suffice for integral parabolicity.','One nonzero integer clears the rational cocycle and all whole-cusp-stabilizer witnesses simultaneously.','The actual original period cocycle retains whole-cusp witnesses under its coefficient isomorphism and rational coordinate projection.','The original nonzero primitive period H1 class lies in the complex span of actual integral parabolic H1 classes.']
route['remaining']='Finite parabolic Hecke-character descent and original Gamma1 arithmetic realization remain open. Integral spanning is not finite descent, nonvanishing of reduction, or a characteristic-zero lift. Diamonds, Galois realization, original all-weight association, automorphy and higher symmetric-power continuation remain. DUB17--20 OPEN; 16/20 unchanged.'
route['preservedFailures']='1156a map_ne_zero is an equivalence; repaired with .mpr. 1158a span-induction index made a variable and corrected native nonzero theorem name. Failed sources preserved before repair; logs retained; no hypothesis or resource limit changed.'
checks=[(p/'SourceParabolicIntegralCoordinateSpan.lean','private theorem integer_coefficient_composition','theorem sourceRationalCuspBinaryCocycle_mem_integralParabolic_span',p/'SourceParabolicBinaryRationalSpan.lean',None,None)]
native=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026\SourceComplexBinaryCocycleSpan.lean')
src=native.read_text(encoding='utf-8');dst=(p/'SourceParabolicIntegralCoordinateSpan.lean').read_text(encoding='utf-8')
assert src[src.index('private theorem integer_coefficient_composition'):src.index('private theorem rational_cocycle_mem_span')].strip()==dst[dst.index('private theorem integer_coefficient_composition'):dst.index('theorem sourceRationalCuspBinaryCocycle_mem_integralParabolic_span')].strip()
orig=(p/'SourceParabolicBinaryRationalSpan.lean').read_text(encoding='utf-8');target=(p/'SourceOriginalIntegralParabolicCocycleSpan.lean').read_text(encoding='utf-8')
assert orig[orig.index('private theorem cocycle_ext_generators'):orig.index('/-- Rational parabolic')].strip()==target[target.index('private theorem cocycle_ext_generators'):target.index('theorem sourceComplexCuspBinaryCocycle_mem_integralParabolic_span')].strip()
route['reuseChecked'] += [dict(path=str(f),sha256=sha(f)) for f in [native,p/'SourceParabolicBinaryRationalSpan.lean']]
route['verbatimHelpers']=['integer_coefficient_composition','cocycle_ext_generators','coordinate_sum','coefficientEval']
write('source-original-integral-parabolic-audit-route-1161.json',json.dumps(route,indent=2)+'\n')
t=(p/'record_parabolic_rational_span_1150.py').read_text(encoding='utf-8')
for a,b in [('source-parabolic-rational-span-1',stem),('source-parabolic-rational-span-audit-route-1150','source-original-integral-parabolic-audit-route-1161'),(old,new),('ScratchOwnership1150','ScratchOwnership1161'),('PARABOLIC RATIONAL SPAN','ORIGINAL INTEGRAL PARABOLIC')]:t=t.replace(a,b)
t=t.replace('(3, 5, 10)',str((len(mods),len(ths+defs),len(edges))))
t=t.replace('all 10 required',f'all {len(edges)} required').replace('requiredProofValueEdges=10',f'requiredProofValueEdges={len(edges)}').replace('proofEdges=10',f'proofEdges={len(edges)}').replace('queries=5',f'queries={len(ths+defs)}')
t=t.replace('== 3','== 8').replace('linterScopes=3','linterScopes=8').replace('modules=3','modules=8')
write('record_original_integral_parabolic_1161.py',t)
t=(p/'audit_parabolic_rational_span_1150.ps1').read_text(encoding='utf-8')
for a,b in [(old,new),('ScratchOwnership1150','ScratchOwnership1161'),('record_parabolic_rational_span_1150','record_original_integral_parabolic_1161')]:t=t.replace(a,b)
write('audit_original_integral_parabolic_1161.ps1',t)
print(json.dumps(dict(modules=len(mods),theorems=len(ths),constructions=len(defs),queries=len(ths+defs),edges=len(edges))))
