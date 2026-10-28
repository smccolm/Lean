from pathlib import Path
from datetime import datetime, timezone
import json,re,hashlib
p=Path(__file__).parent
names=[('SourceParabolicCohomology','1140b'),('SourceBinaryParabolicChange','1141b'),('SourceGammaOneParabolicRestriction','1142e'),('SourceParabolicCoefficientMap','1144a'),('SourcePeriodParabolicClass','1143c'),('SourceOriginalParabolicEigensystem','1145a')]
mods=[n for n,a in names]
ths=[];defs=[]
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
for n,a in names:
 t=(p/(n+'.lean')).read_text(encoding='utf-8')
 t=re.sub(r'/\-.*?\-/', '', t, flags=re.S)
 t=re.sub(r'--[^\n]*', '', t)
 ns=re.search(r'^namespace (\S+)',t,re.M)[1]+'.'
 ths += [ns+x for x in re.findall(r'^theorem (\w+)',t,re.M)]
 defs += [ns+x for x in re.findall(r'^(?:def|abbrev) (\w+)',t,re.M)]
 assert (p/(n+a+'.exit')).read_text().strip()=='0'
 assert (p/(n+a+'.log')).stat().st_size==0
ns='Dubon2026.'
roots=[ns+x for x in ['sourcePrimitive_originalParabolicHeckeWordEigensystem','sourceIntegralBinaryParabolic_gammaOne_reduction','sourceBinaryCocyclesChange_parabolic']]
edges=ths+defs+[ns+x for x in ['SourceParabolic.classification','sourcePeriodCocycle_parabolic','sourcePeriodCoefficientIso','sourcePeriodH1BinaryEquiv_period','sourceBinaryCoefficientMap_equivariant','sourceGammaOneDiagonalHom_binary_trivial','sourcePrimitive_nonzero_integralModelComplexEigensystem','sourceHeckeWord_eigenvector','sourceSemilinearH1','sourceSemilinearCocycles']]
prior=json.loads((p/'source-gamma-one-binary-tate-h1-1-audit-config.json').read_text())
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,roots=roots,proofEdges=edges,localModules=list(dict.fromkeys(mods+prior['localModules'])),separatelyAxiomChecked=[],compileEvidence={n:n+a for n,a in names})
def write(n,t):
 f=p/n;assert not f.exists(),f
 f.write_text(t,encoding='utf-8')
stem='source-original-parabolic-entry-1b'
write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
imports='\n'.join('import '+n for n in mods)+'\nimport Mathlib.Tactic\n'
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
old='SourceGammaOneBinaryTateH1';new='SourceOriginalParabolicEntry'
for suffix,newSuffix in [('Audit1','Audit1b'),('DependencyAudit1','DependencyAudit1b'),('ScratchOwnership1139','ScratchOwnership1146b')]:
 t=(p/(old+suffix+'.lean')).read_text(encoding='utf-8')
 t=imports+t[t.index('\nopen Lean'):]
 if suffix=='Audit1':
  t=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in ths+defs),t,count=1)
  for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:
   t=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),t)
  t=re.sub(r'#lint in [^\n]+\n','',t).rstrip()+'\n\n'+'\n'.join('#lint in '+m for m in mods)+'\n'
 elif suffix=='DependencyAudit1':
  for k,v in [('roots',roots),('localModules',cfg['localModules']),('required',edges)]:
   t=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),t)
  t=t.replace('actual original homogeneous-coefficient arithmetic Tate dual/parabolic H1 equivalence and original whole-word Hecke VALUE closures. Actual levels discharge finite-order vanishing. Full/parabolic passage, diamonds and Galois realization remain','actual original nonzero parabolic Hecke-word eigenclass and literal coefficient-reduction/Gamma1-restriction VALUE closures. Integral parabolic spanning and finite-character descent remain; no nonvanishing or surjectivity of finite restriction is inferred. Diamonds and Galois realization remain')
 else:
  t=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),t)
 t=t.replace('GAMMA ONE BINARY TATE H1','ORIGINAL PARABOLIC ENTRY').replace('Gamma One Binary Tate H1','Original Parabolic Entry')
 write(new+newSuffix+'.lean',t)
routefile=p/'source-original-parabolic-entry-reuse-1140.json'
route=json.loads(routefile.read_text())
route['reuseChecked'].append(dict(path=str(routefile),sha256=sha(routefile)))
route['recordedUTC']=datetime.now(timezone.utc).isoformat()
route['preservedFailures']='1140a cocycle coercion and quotient equality rearrangement; 1141a explicit representation inference; 1142a premature dependency invocation, 1142b/c/d unnecessary nonzero original-level hypotheses removed to fix warnings; 1143a/b large coefficient-equivalence unfolding avoided by the required native representation-morphism lemma. Failed sources and diagnostics preserved before repairs; no proof limits increased.'
route['auditRepair']='1146a declaration extraction incorrectly read the prose line theorem over C as a declaration named over. Fresh b extraction strips comments first; all real 15 theorems and 2 constructions are retained, with the same mathematical sources and 27 actual VALUE edges. The used a audit and diagnostics remain immutable.'
route['dischargedConsumer']='The actual original primitive form gives a nonzero class in literal native parabolic homogeneous H1 and every original Hecke-word eigenvalue. Actual integral coefficient reduction followed by the original diagonal Gamma1 restriction lands in the homogeneous parabolic H1 used by the arithmetic Tate comparison. Neither finite restriction nonvanishing nor finite character descent is concluded.'
write('source-original-parabolic-entry-audit-route-1146b.json',json.dumps(route,indent=2)+'\n')
t=(p/'record_source_gamma_one_binary_tate_h1_1139.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-binary-tate-h1-1',stem),('source-gamma-one-binary-tate-h1-audit-route-1139','source-original-parabolic-entry-audit-route-1146b'),(old,new),('ScratchOwnership1139','ScratchOwnership1146b'),('GAMMA ONE BINARY TATE H1','ORIGINAL PARABOLIC ENTRY'),('20261027','20261028'),('2026-10-27','2026-10-28')]:t=t.replace(a,b)
t=t.replace('(6, 27, 34)',str((len(mods),len(ths+defs),len(edges))))
t=t.replace('all 34 required',f'all {len(edges)} required').replace('requiredProofValueEdges=34',f'requiredProofValueEdges={len(edges)}').replace('proofEdges=34',f'proofEdges={len(edges)}').replace('queries=27',f'queries={len(ths+defs)}')
t=t.replace(new+'Audit1',new+'Audit1b').replace(new+'DependencyAudit1',new+'DependencyAudit1b')
write('record_original_parabolic_entry_1146b.py',t)
t=(p/'audit_gamma_one_binary_tate_h1_1139.ps1').read_text(encoding='utf-8')
for a,b in [(old,new),('ScratchOwnership1139','ScratchOwnership1146b'),('record_source_gamma_one_binary_tate_h1_1139','record_original_parabolic_entry_1146b')]:t=t.replace(a,b)
t=t.replace(new+'Audit1',new+'Audit1b').replace(new+'DependencyAudit1',new+'DependencyAudit1b')
write('audit_original_parabolic_entry_1146b.ps1',t)
print(json.dumps(dict(modules=len(mods),theorems=len(ths),constructions=len(defs),queries=len(ths+defs),edges=len(edges))))
