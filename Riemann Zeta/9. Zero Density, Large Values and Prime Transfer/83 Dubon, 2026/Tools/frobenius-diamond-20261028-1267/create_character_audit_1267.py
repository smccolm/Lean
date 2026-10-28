from pathlib import Path
import ast,re
p=Path(__file__).parent
s=(p/'prepare_diamond_transfer_audit_1262.py').read_text(encoding='utf-8')
a=s.index('mods=');b=s.index('ev=',a)
s=s[:a]+"mods=['SourceGammaOneHeckeDiamondWords','SourceGammaOneHeckeDiamondDescent','SourcePrimitiveGammaOneHeckeDiamondCharacter']\nattempts=['1264a','1265a','1266a']\n"+s[b:]
a=s.index('edges=');b=s.index('def write(',a)
s=s[:a]+'''edges=ths+defs+['Dubon2026.'+x for x in [
 'sourceGammaOneConstantH1Transfer_diamond','sourceGammaOneConstantH1Transfer_surjective',
 'sourcePrimitiveFiniteH1HeckeCharacter_comp','sourcePrimitiveH1AdicQuotientCharacter_hecke',
 'sourceHeckeWord_intertwine_addHom','sourcePrimePower_six_isUnit']]
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,
 roots=['Dubon2026.sourcePrimitiveGammaOneHeckeDiamondCharacter_hecke',
 'Dubon2026.sourcePrimitiveGammaOneHeckeDiamondCharacter_diamond'],proofEdges=edges,
 localModules=mods+json.loads((p/'source-diamond-transfer-1-audit-config.json').read_text(encoding='utf-8'))['modules'],
 separatelyAxiomChecked=[],compileEvidence=ev)
'''+s[b:]
# Reuse the completed diamond-transfer audit template and recorder.
s=s.replace("old='SourceFrobeniusNormalization';new='SourceDiamondTransfer'",
 "old='SourceDiamondTransfer';new='SourceHeckeDiamondCharacter'")
s=s.replace("('ScratchOwnership1250','ScratchOwnership1262')","('ScratchOwnership1262','ScratchOwnership1267')")
s=s.replace("('localModules',mods)","('localModules',cfg['localModules'])")
s=s.replace("s=s.replace('FROBENIUS NORMALIZATION','DIAMOND TRANSFER')",
 "s=s.replace('DIAMOND TRANSFER','HECKE DIAMOND CHARACTER')")
s=s.replace("stem='source-diamond-transfer-1'","stem='source-hecke-diamond-character-1'")
s=s.replace('occur in the proof value closure of the single original Gamma1 native transfer diamond-invariance endpoint, through the actual subgroup normalizer, inverse homogeneous coefficient action and native trace base change. Parabolic preimages, arithmetic character realization and geometric Frobenius/inertia remain unresolved',
 'occur in the proof value closures of the original finite-character Fourier and diamond-one endpoints, through the literal extended operator image, native surjective transfer and original adic character. Parabolic and arithmetic two-dimensional realizations remain unresolved')
a=s.index('reuse=');b=s.index("s=(p/'record_",a)
s=s[:a]+'''reuse=[r/'Extension/Dubon2026'/(m+'.lean') for m in [
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
write('source-hecke-diamond-character-audit-route-1267.json',json.dumps(route,indent=2)+'\\n')
'''+s[b:]
a=s.index("s=(p/'record_")
s=s[:a]+'''s=(p/'record_diamond_transfer_1262.py').read_text(encoding='utf-8')
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
'''
ast.parse(s)
out=p/'prepare_hecke_diamond_character_audit_1267.py';assert not out.exists()
out.write_text(s,encoding='utf-8')
