from pathlib import Path
from datetime import datetime, timezone
import ast, json, re, hashlib
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
mods=['SourceHomogeneousHeckeDiamond','SourceGammaOneHeckeDiamondCoefficient',
 'SourceGammaOneArithmeticTateOperators','SourceTateDualQuadratic',
 'SourceGammaOneBinaryFrobeniusNormalization','SourceCoefficientDualAction',
 'SourceGammaOneBinaryGaloisHecke']
attempts=['1243b','1244b','1246a','1248b','1245h','1249b','1247j']
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
 'binaryHomogeneousMonomialBasis_diagonal_ring',
 'sourceGammaOneBinaryDiamondCoefficient_eq_diagonal',
 'SourceFunctionField.GammaOne.heckePicard_arithmetic',
 'SourceFunctionField.GammaOne.arithmeticDiamondTate_galois',
 'TateModule.mapEnd']]+['LinearMap.lcomp']
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,roots=ths+defs,
 proofEdges=edges,localModules=mods,separatelyAxiomChecked=[],compileEvidence=ev)
def write(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
stem='source-frobenius-normalization-1'
write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
old='SourceDiamondNormalizer';new='SourceFrobeniusNormalization'
for a,b in [('Audit1','Audit1'),('DependencyAudit1','DependencyAudit1'),('ScratchOwnership1241','ScratchOwnership1250')]:
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
  s=s[:start]+' occur in the actual homogeneous coefficient square, original arithmetic Tate Hecke and diamond commutation, conditional original Frobenius normalization, and contragredient Galois compatibility with every native prime Hecke operator. The geometric Gamma1 Frobenius relation, inertia, parabolic character descent, exceptional primes and characteristic-zero association remain unresolved'+s[end:]
 else:
  s=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),s)
 s=s.replace('DIAMOND NORMALIZER','FROBENIUS NORMALIZATION')
 s=s.replace('Gamma One Diamond Period','Frobenius Normalization')
 write(new+b+'.lean',s)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
reuse=[r/'Extension/Dubon2026'/(m+'.lean') for m in [
 'FiniteSymmetricRegularDiagonal','SourceGammaOneDiamondCoefficientMatrix',
 'SourceTateEndomorphisms','SourceGammaOneBinaryTateHecke',
 'SourceGammaOneHeckeArithmetic','SourceGammaOneDiamondGaloisPicard',
 'SourceOriginalPicardFrobeniusQuadratic','SourceOriginalTateFrobeniusQuadratic']]
reuse += [Path(r'E:\Lean\Riemann Zeta\.lake\packages\mathlib\Mathlib')/m
 for m in ['LinearAlgebra/BilinearMap.lean','RepresentationTheory/Basic.lean']]
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),
 chain='DUB17 Theorem 2.6 / DUB18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> original finite Gamma1 homogeneous-coefficient arithmetic Hecke characters -> original Tate Frobenius/inertia realization and Galois-stable character spaces.',
 reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],
 shorterRoute='The existing ring-valued homogeneous monomial-basis diagonal formula proves the exact coefficient square without generalizing the complex scalar-action framework. The original lifted normalizer formula supplies the native inverse diagonal. Reuse the native Tate endomorphism ring homomorphism and proved Picard Hecke/diamond arithmetic commutation. Mathlib lcomp supplies precomposition with codomain scalars and the standard contragredient inverse convention. Split the necessary dual quadratic calculation from original-object instantiation to stay within unchanged proof limits. The native original Gamma0 function-field reduction already proves Frobenius and inertia; extending its exact Gamma1 geometric relation remains preferable to importing a new scheme dependency chain before a need is established.',
 assumptionsToDischarge=[
 'At every homogeneous degree and positive coefficient modulus, the original Hecke coefficient squared equals ell^w times the actual normalizer diamond coefficient whenever its lower-right label is ell.',
 'The actual Gamma1 Tate Galois representation commutes with the original arithmetic Picard Hecke and diamond operators.',
 'Given the explicitly stated original Gamma1 Tate geometric relation H*F=F*F+ell*D, the literal homogeneous-valued dual satisfies the normalized relation with ell^(w+1) times the original coefficient diamond. This conclusion is conditional on that geometric relation, not a proof of it.',
 'The genuine inverse-precomposition Galois representation on the original homogeneous-valued Tate dual commutes with every native prime Hecke operator. This is the required generator compatibility; no original two-dimensional character space is constructed here.'],
 remaining='The actual Gamma1 geometric Frobenius relation and inertia are not proved by this scope. The original integral parabolic-transfer condition, fixed exceptional-prime exclusion, coefficient-field realization, original all-weight characteristic-zero association, local/image/regularity, automorphy and literal higher continuation remain. Finite characters and a Galois action on the ambient Tate dual do not supply a two-dimensional characteristic-zero association. 16/20; DUB17--20 OPEN.',
 preservedFailures='All failed variants are retained as inert source snapshots with original logs. Dependent exponent rewriting was replaced by a fixed-base power equality. Native Tate field presentations and broad rewrites exceeded default limits; typed original operator names and the small dual calculation remove repeated unfolding. The separate optional word-commutation wrapper was not retained after elaboration failures: the needed native prime-generator compatibility is proved, and existing integral-word and generated-algebra APIs remain available when character-space construction consumes it. SourceHeckeWordCommutation is an unpromoted scratch experiment, not part of this scope. No existing word or acceptance contract is weakened. No limits were increased.',
 externalBuild=False,externalImport=False,rootPinsChanged=False)
write('source-frobenius-normalization-audit-route-1250.json',json.dumps(route,indent=2)+'\n')
s=(p/'record_diamond_normalizer_1241.py').read_text(encoding='utf-8')
for a,b in [('source-diamond-normalizer-audit-route-1241','source-frobenius-normalization-audit-route-1250'),
 ('source-diamond-normalizer-1',stem),(old,new),('ScratchOwnership1241','ScratchOwnership1250'),
 ('DIAMOND NORMALIZER','FROBENIUS NORMALIZATION')]:s=s.replace(a,b)
s=s.replace('(5, 13, 20)',str((len(mods),len(ths+defs),len(edges))))
s=s.replace('== 5','== 7').replace('linterScopes=5','linterScopes=7').replace('modules=5','modules=7')
s=s.replace('all 20 required',f'all {len(edges)} required').replace('requiredProofValueEdges=20',f'requiredProofValueEdges={len(edges)}')
s=s.replace('proofEdges=20',f'proofEdges={len(edges)}').replace('queries=13',f'queries={len(ths+defs)}')
ast.parse(s);write('record_frobenius_normalization_1250.py',s)
s=(p/'audit_diamond_normalizer_1241.ps1').read_text(encoding='utf-8')
for a,b in [(old,new),('ScratchOwnership1241','ScratchOwnership1250'),('record_diamond_normalizer_1241','record_frobenius_normalization_1250')]:s=s.replace(a,b)
write('audit_frobenius_normalization_1250.ps1',s)
print(json.dumps(dict(modules=len(mods),theorems=len(ths),constructions=len(defs),queries=len(ths+defs),edges=len(edges))))
