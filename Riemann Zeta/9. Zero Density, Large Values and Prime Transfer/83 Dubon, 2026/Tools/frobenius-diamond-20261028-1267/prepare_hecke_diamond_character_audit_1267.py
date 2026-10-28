from pathlib import Path
from datetime import datetime, timezone
import ast, json, re, hashlib
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
mods=['SourceGammaOneHeckeDiamondWords','SourceGammaOneHeckeDiamondDescent','SourcePrimitiveGammaOneHeckeDiamondCharacter']
attempts=['1264a','1265a','1266a']
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
 'sourceGammaOneConstantH1Transfer_diamond','sourceGammaOneConstantH1Transfer_surjective',
 'sourcePrimitiveFiniteH1HeckeCharacter_comp','sourcePrimitiveH1AdicQuotientCharacter_hecke',
 'sourceHeckeWord_intertwine_addHom','sourcePrimePower_six_isUnit']]
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,
 roots=['Dubon2026.sourcePrimitiveGammaOneHeckeDiamondCharacter_hecke',
 'Dubon2026.sourcePrimitiveGammaOneHeckeDiamondCharacter_diamond'],proofEdges=edges,
 localModules=mods+json.loads((p/'source-diamond-transfer-1-audit-config.json').read_text(encoding='utf-8'))['modules'],
 separatelyAxiomChecked=[],compileEvidence=ev)
def write(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
stem='source-hecke-diamond-character-1'
write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
old='SourceDiamondTransfer';new='SourceHeckeDiamondCharacter'
for a,b in [('Audit1','Audit1'),('DependencyAudit1','DependencyAudit1'),('ScratchOwnership1262','ScratchOwnership1267')]:
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
  s=s[:start]+' occur in the proof value closures of the original finite-character Fourier and diamond-one endpoints, through the literal extended operator image, native surjective transfer and original adic character. Parabolic and arithmetic two-dimensional realizations remain unresolved'+s[end:]
 else:
  s=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),s)
 s=s.replace('DIAMOND TRANSFER','HECKE DIAMOND CHARACTER')
 write(new+b+'.lean',s)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
reuse=[r/'Extension/Dubon2026'/(m+'.lean') for m in [
 'SourceGammaOneHeckeWords','SourceGammaOneOperatorDescent',
 'SourcePrimitiveGammaOneHeckeCharacter','SourcePrimitiveFiniteH1HeckeCharacter',
 'SourceFiniteOperatorCharacterDescent','SourceBinaryPermutationHeckeWords']]
reuse += [p/'SourceGammaOneDiamondTransfer.lean']
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),
 chain='DUB17 Theorem 2.6 / DUB18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> original finite Gamma1 arithmetic character realization -> diamond-one character needed for the normalized Frobenius determinant.',
 reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],
 shorterRoute='Extend the existing literal prime-operator algebra by the actual homogeneous normalizer diamonds. Reuse the existing additive whole-word intertwiner, native transfer surjectivity and operator-kernel descent; do not develop a new trace or eigensystem framework. The original adic character then gives both the original Fourier values and diamond value one.',
 assumptionsToDischarge=[
 'The original native transfer intertwines every word in actual prime Hecke and homogeneous normalizer diamond operators, with diamonds acting as one on the original Gamma0 coefficient module.',
 'When six is a unit, every relation in this literal extended operator image descends to the original finite tensor-operator image; no kernel inclusion is assumed.',
 'For each original primitive form of weight at least two, prescribed coefficient-field embedding, prime p greater than three and every precision p^(n+1), the actual extended Gamma1 operator image has a character retaining all original good-prime Fourier values and taking every original homogeneous normalizer diamond to one.'],
 remaining='The character is constructed on full H1. Its parabolic factorization and two-dimensional arithmetic realization are not supplied. The original Gamma1 geometric Frobenius relation and inertia, parabolic preimages or a faithful alternative, exceptional primes, coefficient-field realization, characteristic-zero association, local/image/regularity, automorphy and literal higher continuation remain. 16/20; DUB17--20 OPEN.',
 preservedFailures='The original prime-only descent and character proofs are reused on the actual enlarged operator image. No proof limits changed. The inert preparation scripts record construction of each new source; the final compiled and audited bodies are hashed separately.',
 externalBuild=False,externalImport=False,rootPinsChanged=False)
write('source-hecke-diamond-character-audit-route-1267.json',json.dumps(route,indent=2)+'\n')
s=(p/'record_diamond_transfer_1262.py').read_text(encoding='utf-8')
for a,b in [('source-diamond-transfer-audit-route-1262','source-hecke-diamond-character-audit-route-1267'),
 ('source-diamond-transfer-1',stem),(old,new),('ScratchOwnership1262','ScratchOwnership1267'),
 ('DIAMOND TRANSFER','HECKE DIAMOND CHARACTER')]:s=s.replace(a,b)
s=s.replace('(9, 14, 20)',str((len(mods),len(ths+defs),len(edges))))
s=s.replace('== 9','== 3').replace('linterScopes=9','linterScopes=3').replace('modules=9','modules=3')
ast.parse(s);write('record_hecke_diamond_character_1267.py',s)
s=(p/'audit_diamond_transfer_1262.ps1').read_text(encoding='utf-8')
for a,b in [(old,new),('ScratchOwnership1262','ScratchOwnership1267'),('record_diamond_transfer_1262','record_hecke_diamond_character_1267')]:s=s.replace(a,b)
write('audit_hecke_diamond_character_1267.ps1',s)
print(json.dumps(dict(modules=len(mods),theorems=len(ths),constructions=len(defs),queries=len(ths+defs),edges=len(edges))))
