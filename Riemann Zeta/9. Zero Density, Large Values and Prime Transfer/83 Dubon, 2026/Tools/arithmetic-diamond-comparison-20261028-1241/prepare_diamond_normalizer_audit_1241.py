from pathlib import Path
from datetime import datetime, timezone
import ast, json, re, hashlib
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
mods=['SourceGammaOneDiamondCoefficient','SourceGammaOneDiamondRestriction',
 'SourceGammaOneDiamondCoefficientMatrix','SourceGammaOneBinaryNormalizerTate',
 'SourceGammaOneBinaryDiamondLabels']
attempts=['1235b','1236b','1237c','1239b','1240a']
ev=dict(zip(mods,[m+a for m,a in zip(mods,attempts)]))
ths=[];defs=[]
for m in mods:
 assert (p/(ev[m]+'.exit')).read_text().strip()=='0'
 assert (p/(ev[m]+'.log')).stat().st_size==0
 raw=(p/(m+'.lean')).read_text(encoding='utf-8')
 ns=re.search(r'^namespace (\S+)',raw,re.M)[1]+'.'
 code=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',raw,flags=re.S))
 ths += [ns+x for x in re.findall(r'^theorem\s+([\w.]+)',code,re.M)]
 defs += [ns+x for x in re.findall(r'^def\s+([\w.]+)',code,re.M)]
edges=ths+defs+['Dubon2026.'+x for x in [
 'sourceRaisedLevelConjugation','sourceGammaOneDiagonalHom_binary_trivial',
 'sourceGammaOneBinaryRestrictionH1_cocycle','sourceGammaOneDiamondH1_hom_apply',
 'sourceGammaOneDiamondH1_lift_independent',
 'SourceFunctionField.GammaOne.binaryTateH1Equiv_diamond',
 'SourceFunctionField.GammaOne.arithmeticDiamondTate_galois']]
prior=json.loads((p/'source-diamond-galois-1-audit-config.json').read_text())
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,roots=ths+defs,
 proofEdges=edges,localModules=mods+prior['localModules'],separatelyAxiomChecked=[],compileEvidence=ev)
def write(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
stem='source-diamond-normalizer-1'
write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
old='SourceDiamondGalois';new='SourceDiamondNormalizer'
for a,b in [('Audit1','Audit1'),('DependencyAudit1','DependencyAudit1'),('ScratchOwnership1234','ScratchOwnership1241')]:
 s=(p/(old+a+'.lean')).read_text(encoding='utf-8')
 s='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+s[s.index('\nopen Lean'):]
 if a=='Audit1':
  s=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in cfg['queries']),s,count=1)
  for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:
   s=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),s)
  s=re.sub(r'#lint in [^\n]+\n','',s).rstrip()+'\n\n'+''.join('#lint in '+m+'\n' for m in mods)
 elif a=='DependencyAudit1':
  for k,v in [('roots',cfg['roots']),('localModules',cfg['localModules']),('required',edges)]:
   s=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),s)
  start=s.index(' occur in the ');end=s.index('; DUB17--20 OPEN.',start)
  s=s[:start]+' occur in the original lifted normalizer and its inverse binary coefficient action, original cocycle/H1 restriction invariance, exact homogeneous diagonal substitution, arithmetic Tate/H1 and Galois comparison, and lift independence. Parabolic transfer preimages, exceptional primes, Frobenius/inertia, characteristic-zero association and higher continuation remain unresolved'+s[end:]
 else:
  s=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),s)
 s=s.replace('DIAMOND GALOIS','DIAMOND NORMALIZER')
 write(new+b+'.lean',s)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
reuse=[p/'source-diamond-galois-1-scratch-receipt.json',p/'SourceGammaOneDiamondLabels.lean']
reuse += [r/'Extension/Dubon2026'/(m+'.lean') for m in [
 'SourceGammaOneDiagonalHom','SourceRaisedLevelConjugation','SourceGammaOneBinaryRestriction',
 'SourceIntegralCohomologyFinite','HomogeneousDiagonalAction']]
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),
 chain='DUB17 Theorem 2.6 / DUB18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight association -> original finite Gamma1 homogeneous-coefficient arithmetic realization -> original homogeneous normalizer diamond comparison.',
 reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],
 shorterRoute='Restrict the existing raised-level group homomorphism to the actual Gamma0 normalizer. Native cocycle multiplication and proved diagonal-cover coefficient triviality give exact restriction invariance. Original matrix entries modulo N identify the inverse coefficient action with the existing homogeneous diagonal substitution. Compose the already audited arithmetic Tate/H1 diamond equality with this matrix equality; use the proved arithmetic Picard Tate Galois commutation. The original Gamma1 character kernel and coefficient triviality give lift independence. No new normalizer or cohomology framework is needed.',
 assumptionsToDischarge=[
 'The inverse lifted normalizer action intertwines the original binary representation under the actual Gamma1 conjugation.',
 'The resulting diamond fixes literal restrictions of every original binary cocycle and H1 class.',
 'At every positive coefficient modulus and every homogeneous degree, the original inverse normalizer action equals homogeneous substitution by the reversed diagonal entries modulo that modulus.',
 'The original arithmetic Picard Tate dual acts on native finite Gamma1 H1 by this exact homogeneous coefficient convention and commutes with original arithmetic Galois.',
 'The original coefficient action and resulting native H1 diamond depend only on the lower-right unit label.'],
 remaining='Supersedes the unresolved homogeneous normalizer coefficient convention in scope 1234. Parabolic transfer preimages, the fixed exceptional-prime exclusion, coefficient-field/Frobenius/inertia realization, characteristic-zero all-weight association, automorphy and literal higher continuation remain. Finite characters do not supply a characteristic-zero lift. 16/20; DUB17--20 OPEN.',
 preservedFailures='1237a mapGL matrix coercion rewrite and unused simp fixed using the literal mapped matrix. 1239a broad rewrite exceeded default heartbeats; repaired by explicit composition of the two proved equalities. Successful 1235a/1236a/1237b retained before uniform scratch-import rebuilding. No proof limits or standards changed.',
 externalBuild=False,externalImport=False,rootPinsChanged=False)
write('source-diamond-normalizer-audit-route-1241.json',json.dumps(route,indent=2)+'\n')
s=(p/'record_diamond_galois_1234.py').read_text(encoding='utf-8')
for a,b in [('source-diamond-galois-audit-route-1234','source-diamond-normalizer-audit-route-1241'),
 ('source-diamond-galois-1',stem),(old,new),('ScratchOwnership1234','ScratchOwnership1241'),
 ('DIAMOND GALOIS','DIAMOND NORMALIZER')]:s=s.replace(a,b)
s=s.replace('(13, 22, 34)',str((len(mods),len(ths+defs),len(edges))))
s=s.replace('== 13','== 5').replace('linterScopes=13','linterScopes=5').replace('modules=13','modules=5')
s=s.replace('all 34 required',f'all {len(edges)} required').replace('requiredProofValueEdges=34',f'requiredProofValueEdges={len(edges)}')
s=s.replace('proofEdges=34',f'proofEdges={len(edges)}').replace('queries=22',f'queries={len(ths+defs)}')
ast.parse(s);write('record_diamond_normalizer_1241.py',s)
s=(p/'audit_diamond_galois_1234.ps1').read_text(encoding='utf-8')
for a,b in [(old,new),('ScratchOwnership1234','ScratchOwnership1241'),('record_diamond_galois_1234','record_diamond_normalizer_1241')]:s=s.replace(a,b)
write('audit_diamond_normalizer_1241.ps1',s)
print(json.dumps(dict(modules=len(mods),theorems=len(ths),constructions=len(defs),queries=len(ths+defs),edges=len(edges))))
