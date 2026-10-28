from pathlib import Path
from datetime import datetime, timezone
import ast, json, re, hashlib
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
mods=['SourceInnerH1Identity','SourceH1TraceInner','SourceGammaOneDiamondRange',
 'SourceH1TraceSubgroupEquality','SourceNormalizerH1Trace','SourceH1CompositionSquare',
 'SourceNormalizerCoefficientValue','SourceGammaOneDiamondSubgroupSquare','SourceGammaOneDiamondTransfer']
attempts=['1253d','1254a','1255a','1256a','1257b','1260a','1261a','1258c','1259b']
ev={m:m+a for m,a in zip(mods,attempts)}
ths=[];defs=[]
for m in mods:
 assert (p/(ev[m]+'.exit')).read_text().strip()=='0'
 assert (p/(ev[m]+'.log')).stat().st_size==0
 raw=(p/(m+'.lean')).read_text(encoding='utf-8')
 code=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',raw,flags=re.S))
 ths += ['Dubon2026.'+x for x in re.findall(r'^theorem\s+([\w.]+)',code,re.M)]
 defs += ['Dubon2026.'+x for x in re.findall(r'^def\s+([\w.]+)',code,re.M)]
edges=ths+defs+['Dubon2026.'+x for x in [
 'sourceSubgroupH1Trace_pullback_coefficient',
 'sourceGammaOneSubgroupH1Iso_hom_eq_map',
 'sourceGammaOneConstantH1Transfer_subgroupIso',
 'sourceHeckeH1Trace_eq_subgroupTrace',
 'sourceGammaOneDiamondLift_conjugation']]+['groupCohomology.map_comp']
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,
 roots=['Dubon2026.sourceGammaOneConstantH1Transfer_diamond'],proofEdges=edges,
 localModules=mods,separatelyAxiomChecked=[],compileEvidence=ev)
def write(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
stem='source-diamond-transfer-1'
write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
old='SourceFrobeniusNormalization';new='SourceDiamondTransfer'
for a,b in [('Audit1','Audit1'),('DependencyAudit1','DependencyAudit1'),('ScratchOwnership1250','ScratchOwnership1262')]:
 s=(p/(old+a+'.lean')).read_text(encoding='utf-8')
 s='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+s[s.index('\nopen Lean'):]
 if a=='Audit1':
  s=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in cfg['queries']),s,count=1)
  for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:
   s=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),s)
  s=re.sub(r'#lint in [^\n]+\n','',s).rstrip()+'\n\n'+''.join('#lint in '+m+'\n' for m in mods)
 elif a=='DependencyAudit1':
  for k,v in [('roots',cfg['roots']),('localModules',mods),('required',edges)]:
   s=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),s)
  start=s.index(' occur in the ');end=s.index('; DUB17--20 OPEN.',start)
  s=s[:start]+' occur in the proof value closure of the single original Gamma1 native transfer diamond-invariance endpoint, through the actual subgroup normalizer, inverse homogeneous coefficient action and native trace base change. Parabolic preimages, arithmetic character realization and geometric Frobenius/inertia remain unresolved'+s[end:]
 else:
  s=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),s)
 s=s.replace('FROBENIUS NORMALIZATION','DIAMOND TRANSFER')
 write(new+b+'.lean',s)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
reuse=[r/'Extension/Dubon2026'/(m+'.lean') for m in [
 'SourceH1TraceBaseChangeCoefficient','SourceGammaOneHeckePullbackSquare',
 'SourceGammaOneSubgroupCohomologyMap','SourceGammaOneDiamondCoefficient',
 'SourceGammaOneDiamondH1','SourceGammaOneTransferCosetFormula','SourceShapiroH1CosetTrace']]
reuse += [Path(r'E:\Lean\Riemann Zeta\.lake\packages\mathlib\Mathlib')/m
 for m in ['RepresentationTheory/Homological/GroupCohomology/Functoriality.lean',
 'RepresentationTheory/Homological/GroupCohomology/LowDegree.lean']]
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),
 chain='DUB17 Theorem 2.6 / DUB18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> original finite Gamma1 homogeneous-coefficient arithmetic Hecke characters -> diamond-one descent from the original Gamma0 character, needed for the normalized Frobenius determinant.',
 reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],
 shorterRoute='Reuse the existing native trace base-change theorem and original subgroup H1 isomorphism. Prove inner conjugation with inverse coefficient action is the identity by its explicit coboundary, then transport the native trace through the proved subgroup equality. Reuse the group/coefficient composition proof already present in the original Hecke pullback square instead of elaborating the entire concrete cocycle square. No replacement transfer, new cohomology framework, broader degree generalization, or unit hypothesis is introduced.',
 assumptionsToDischarge=[
 'The actual lifted original Gamma0 normalizer preserves the exact range of the original diagonal-cover homomorphism.',
 'Under the existing subgroup H1 isomorphism, native normalizer pullback with inverse coefficient action is the original Gamma1 diamond with its original homogeneous coefficient.',
 'For every positive original level and coefficient modulus, every homogeneous degree, every original normalizer and every full H1 class, the literal native transfer of its original diamond image equals its original transfer. No six-unit or parabolic-preimage assumption is needed.'],
 remaining='This proves diamond invariance of the full native transfer, not existence of parabolic preimages or construction of a parabolic arithmetic character space. The actual Gamma1 geometric Frobenius relation and inertia, original integral parabolic-transfer condition, exceptional-prime exclusion, coefficient-field realization, original all-weight characteristic-zero association, local/image/regularity, automorphy and literal higher continuation remain. 16/20; DUB17--20 OPEN.',
 preservedFailures='Failed elaborations are preserved as inert sources and original logs. The inner cocycle proof uses the exact Mathlib inverse-cocycle convention. Subgroup equality transport is retained explicitly. A concrete nested cohomology elaboration exceeded the default limit; the existing generic composition-square proof removes that unfolding. No limits increased.',
 externalBuild=False,externalImport=False,rootPinsChanged=False)
write('source-diamond-transfer-audit-route-1262.json',json.dumps(route,indent=2)+'\n')
s=(p/'record_frobenius_normalization_1250.py').read_text(encoding='utf-8')
for a,b in [('source-frobenius-normalization-audit-route-1250','source-diamond-transfer-audit-route-1262'),
 ('source-frobenius-normalization-1',stem),(old,new),('ScratchOwnership1250','ScratchOwnership1262'),
 ('FROBENIUS NORMALIZATION','DIAMOND TRANSFER')]:s=s.replace(a,b)
s=s.replace('(7, 14, 20)',str((len(mods),len(ths+defs),len(edges))))
s=s.replace('== 7','== 9').replace('linterScopes=7','linterScopes=9').replace('modules=7','modules=9')
s=s.replace('all 20 required',f'all {len(edges)} required').replace('requiredProofValueEdges=20',f'requiredProofValueEdges={len(edges)}')
s=s.replace('proofEdges=20',f'proofEdges={len(edges)}').replace('queries=14',f'queries={len(ths+defs)}')
ast.parse(s);write('record_diamond_transfer_1262.py',s)
s=(p/'audit_frobenius_normalization_1250.ps1').read_text(encoding='utf-8')
for a,b in [(old,new),('ScratchOwnership1250','ScratchOwnership1262'),('record_frobenius_normalization_1250','record_diamond_transfer_1262')]:s=s.replace(a,b)
write('audit_diamond_transfer_1262.ps1',s)
print(json.dumps(dict(modules=len(mods),theorems=len(ths),constructions=len(defs),queries=len(ths+defs),edges=len(edges))))
