from pathlib import Path
from datetime import datetime,timezone
import json,re,hashlib
p=Path(__file__).parent
names=[('SourceParabolicBinaryCoordinates','1147a'),('SourceParabolicBinaryRationalSpan','1148a'),('SourceParabolicBinaryH1RationalSpan','1149b')]
mods=[n for n,a in names];ths=[];defs=[]
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
for n,a in names:
 t=(p/(n+'.lean')).read_text(encoding='utf-8')
 t=re.sub(r'/\-.*?\-/', '', t, flags=re.S);t=re.sub(r'--[^\n]*','',t)
 ns=re.search(r'^namespace (\S+)',t,re.M)[1]+'.'
 ths += [ns+x for x in re.findall(r'^theorem (\w+)',t,re.M)]
 defs += [ns+x for x in re.findall(r'^(?:def|abbrev) (\w+)',t,re.M)]
 assert (p/(n+a+'.exit')).read_text().strip()=='0' and (p/(n+a+'.log')).stat().st_size==0
roots=['Dubon2026.sourcePrimitive_originalParabolicH1_mem_rational_span']
edges=ths+defs+['Dubon2026.'+x for x in ['sourceHomogeneousAdditiveMap_matrix','sourceBinaryAdditiveCocycles','sourceComplexBinaryCocycleCoordinate','sourceBinaryH1Change_cocycle','sourceOriginalBinaryPeriodCohomology_parabolic']]
prior=json.loads((p/'source-original-parabolic-entry-1b-audit-config.json').read_text())
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,roots=roots,proofEdges=edges,localModules=list(dict.fromkeys(mods+prior['localModules'])),separatelyAxiomChecked=[],compileEvidence={n:n+a for n,a in names})
def write(n,t):
 f=p/n;assert not f.exists(),f
 f.write_text(t,encoding='utf-8')
stem='source-parabolic-rational-span-1'
write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
imports='\n'.join('import '+n for n in mods)+'\nimport Mathlib.Tactic\n'
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
old='SourceOriginalParabolicEntry';new='SourceParabolicRationalSpan'
for suffix,newSuffix in [('Audit1b','Audit1'),('DependencyAudit1b','DependencyAudit1'),('ScratchOwnership1146b','ScratchOwnership1150')]:
 t=(p/(old+suffix+'.lean')).read_text(encoding='utf-8');t=imports+t[t.index('\nopen Lean'):]
 if suffix=='Audit1b':
  t=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in ths+defs),t,count=1)
  for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:t=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),t)
  t=re.sub(r'#lint in [^\n]+\n','',t).rstrip()+'\n\n'+'\n'.join('#lint in '+m for m in mods)+'\n'
 elif suffix=='DependencyAudit1b':
  for k,v in [('roots',roots),('localModules',cfg['localModules']),('required',edges)]:t=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),t)
  t=t.replace('actual original nonzero parabolic Hecke-word eigenclass and literal coefficient-reduction/Gamma1-restriction VALUE closures. Integral parabolic spanning and finite-character descent remain; no nonvanishing or surjectivity of finite restriction is inferred. Diamonds and Galois realization remain','actual original primitive period-class rational parabolic span VALUE closure. Rational coordinates preserve actual local coboundaries. Uniform integral parabolic denominator clearing, integral spanning, finite character descent, diamonds and Galois realization remain')
 else:t=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),t)
 t=t.replace('ORIGINAL PARABOLIC ENTRY','PARABOLIC RATIONAL SPAN').replace('Original Parabolic Entry','Parabolic Rational Span')
 write(new+newSuffix+'.lean',t)
rf=p/'source-parabolic-rational-span-reuse-1147.json';route=json.loads(rf.read_text())
route['reuseChecked'].append(dict(path=str(rf),sha256=sha(rf)))
route['assumptionsToDischarge']=['Actual additive rational-coordinate projection preserves original homogeneous parabolic cocycles by projecting the local coboundary witness.','Every original complex parabolic cocycle is in the complex span of the actual rational parabolic cocycles.','The native H1 quotient preserves this rational span, and the original primitive period class lies in it.']
route['preservedFailures']='1148 unexecuted PowerShell pipeline Unicode encoding corrected before compilation, with original text preserved; 1149a dependent span induction fixed by clearing the already consumed parabolic premise. No statement or proof limit changed.'
native=p/'SourceParabolicBinaryRationalSpan.lean'
orig=Path(route['reuseChecked'][2]['path'])
nt=native.read_text(encoding='utf-8');ot=orig.read_text(encoding='utf-8')
nh=nt[nt.index('private theorem cocycle_ext_generators'):nt.index('private def coefficientEval')].strip()
oh=ot[ot.index('private theorem cocycle_ext_generators'):ot.index('private theorem integer_coefficient_composition')].strip()
assert nh==oh
route['verbatimPrivateHelperReuse']=dict(source=str(orig),sourceSha256=sha(orig),target=str(native),identicalHelpers=['cocycle_ext_generators','coordinate_sum'])
write('source-parabolic-rational-span-audit-route-1150.json',json.dumps(route,indent=2)+'\n')
t=(p/'record_original_parabolic_entry_1146b.py').read_text(encoding='utf-8')
for a,b in [('source-original-parabolic-entry-1b',stem),('source-original-parabolic-entry-audit-route-1146b','source-parabolic-rational-span-audit-route-1150'),(old,new),('ScratchOwnership1146b','ScratchOwnership1150'),('Audit1b','Audit1'),('ORIGINAL PARABOLIC ENTRY','PARABOLIC RATIONAL SPAN')]:t=t.replace(a,b)
t=t.replace('(6, 17, 27)',str((len(mods),len(ths+defs),len(edges))))
t=t.replace('all 27 required',f'all {len(edges)} required').replace('requiredProofValueEdges=27',f'requiredProofValueEdges={len(edges)}').replace('proofEdges=27',f'proofEdges={len(edges)}').replace('queries=17',f'queries={len(ths+defs)}')
t=t.replace('== 6','== 3').replace('linterScopes=6','linterScopes=3').replace('modules=6','modules=3')
write('record_parabolic_rational_span_1150.py',t)
t=(p/'audit_original_parabolic_entry_1146b.ps1').read_text(encoding='utf-8')
for a,b in [(old,new),('ScratchOwnership1146b','ScratchOwnership1150'),('Audit1b','Audit1'),('record_original_parabolic_entry_1146b','record_parabolic_rational_span_1150')]:t=t.replace(a,b)
write('audit_parabolic_rational_span_1150.ps1',t)
print(json.dumps(dict(modules=len(mods),theorems=len(ths),constructions=len(defs),queries=len(ths+defs),edges=len(edges))))
