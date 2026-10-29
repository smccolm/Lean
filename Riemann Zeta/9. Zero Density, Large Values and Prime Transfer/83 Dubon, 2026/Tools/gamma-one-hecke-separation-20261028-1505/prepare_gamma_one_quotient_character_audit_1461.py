from pathlib import Path
from datetime import datetime,timezone
import ast,hashlib,json,re
s=Path(__file__).parent
versions=json.loads((s/'gamma-one-quotient-character-versions-1460.json').read_text(encoding='utf-8'))
mods=list(versions);ths=[];defs=[]
for m in mods:
 code=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',(s/(m+'.lean')).read_text(encoding='utf-8'),flags=re.S))
 ns=re.search(r'^namespace (\S+)',code,re.M)[1]+'.'
 ths += [ns+x for x in re.findall(r'^theorem\s+([\w.\x27]+)',code,re.M)]
 defs += [ns+x for x in re.findall(r'^(?:def|instance)\s+([\w.\x27]+)',code,re.M)]
gn='Dubon2026.SourceFunctionField.GammaOne.';cr=gn+'CoefficientReduction.'
roots=[cr+'exists_gammaOne_diamond_quotient_original_character_of_degree_genus_transfer',gn+'binaryDiamondQuotientGaloisRep_word_of_intertwining',cr+'gammaOne_diamond_quotient_hecke_frobenius_of_intertwining']
edges=ths+['Dubon2026.rationalPrimeOriginalNorm_exists_frobenius','Dubon2026.sourceRationalLocalValuation_frobenius','Dubon2026.sourceRationalLocalValuation_prime','Dubon2026.SourceFunctionField.GaussReduction.residue_charP_of_prime_mem_nonunits',cr+'gammaOne_diamond_relations_hecke_of_degree_genus_eq',gn+'binaryDiamondQuotientOriginalTransfer_parabolic_preimage',gn+'binaryDiamondQuotientOriginalTransfer_hecke_of_intertwining','Dubon2026.sourceHeckeWord_intertwine_addHom','Dubon2026.sourceGammaOneOriginalHeckeWord_change','Dubon2026.sourcePrimitiveParabolicH1AdicQuotientCharacter_zero','Dubon2026.sourceFiniteOperatorCharacterDescend','Dubon2026.sourceFiniteOperatorCharacterDescend_comp',gn+'binaryArithmeticTateGaloisRep_prime',gn+'binaryDiamondQuotientGaloisRep_mk',cr+'gammaOne_diamond_quotient_frobenius_of_degree_genus_eq','Submodule.mapQ','IsAlgClosed.lift',gn+'binaryDiamondQuotientGaloisRep','Dubon2026.sourcePrimitiveH1AdicQuotientCharacter',gn+'binaryDiamondQuotientOriginalTransfer']
assert (len(mods),len(ths),len(defs),len(edges))==(10,12,1,32)
assert len(set(edges))==len(edges)
prior=json.loads((s/'source-gamma-one-diamond-transfer-1-audit-config.json').read_text(encoding='utf-8'))['localModules']
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,roots=roots,proofEdges=edges,localModules=list(dict.fromkeys(prior+mods)),separatelyAxiomChecked=defs,compileEvidence={m:m+'-1460' for m in mods})
def write(n,c):
 t=s/n;assert not t.exists(),t;t.write_text(c,encoding='utf-8')
stem='source-gamma-one-quotient-character-1';write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
old,new='SourceGammaOneDiamondTransfer','SourceGammaOneQuotientCharacter'
for a,b in [('Audit1','Audit1'),('DependencyAudit1','DependencyAudit1'),('ScratchOwnership1447','ScratchOwnership1461')]:
 c=(s/(old+a+'.lean')).read_text(encoding='utf-8')
 c='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+c[c.index('\nopen Lean'):]
 if a=='Audit1':
  c=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in cfg['queries']),c,count=1)
  for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:c=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),c)
  c=re.sub(r'#lint in [^\n]+\n','',c).rstrip()+'\n\n'+''.join('#lint in '+m+'\n' for m in mods)
 elif a=='DependencyAudit1':
  for k,v in [('roots',roots),('localModules',cfg['localModules']),('required',edges)]:c=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),c)
  start=c.index(' occur in the ');end=c.index('; DUB17--20 OPEN.',start)
  c=c[:start]+' occur in the proof value closure of the actual all-good-prime quotient Hecke family and original adic character, its Galois commutation and chosen-operator Frobenius identity. Local Frobenius witnesses, coefficient-prime invertibility, operator descent and character kernel are derived. Original degree/genus families and integral parabolic transfer remain explicit, with 3<p and the original exceptional-integer exclusion'+c[end:]
 else:c=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),c)
 c=c.replace('GAMMA ONE DIAMOND TRANSFER','GAMMA ONE QUOTIENT CHARACTER')
 write(new+b+'.lean',c)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
src=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
routefiles=[s/'gamma-one-local-hecke-reuse-1449.json',s/'gamma-one-quotient-character-reuse-1451.json']
rr=[json.loads(f.read_text(encoding='utf-8')) for f in routefiles]
reuse=list(dict.fromkeys(routefiles+[Path(row['path']) for r in rr for row in r['reuse']]+[s/'SourceGammaOneTwistedGaloisHecke.lean',s/'SourceGammaOneDiamondQuotientGalois.lean',s/'SourceGammaOneDiamondQuotientPolynomial.lean',src/'SourceArithmeticLocalEmbeddingExtension.lean']))
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain=rr[0]['chain'],reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],shorterRoute=[r['selected'] for r in rr]+['Only existence of a global-to-local embedding is needed for Hecke stability. Native IsAlgClosed.lift replaces the stronger prescribed arithmetic-embedding extension in this consumer.','Use the projected Frobenius identity directly for a chosen quotient operator; avoid unpacking another redundant operator witness.','Reuse native Galois/Hecke commutation and additive whole-word transport for the quotient operator algebra.'],assumptionsToDischarge=['Derive the original local decomposition/Frobenius witness and coefficient-prime invertibility at every actual good prime.','Construct the complete actual quotient Hecke family from separate original coordinate-degree and genus families.','Use actual Tate/H1 transfer and exact original parabolic preimages to derive the whole-word kernel inclusion and original adic character on the literal operator image.','Retain Galois commutation for all integral words and the exact Frobenius identity for the chosen original operators.'],remaining='Coordinate-degree and genus preservation and the original integral parabolic-transfer theorem remain open. The character comparison retains 3<p and avoidance of the original fixed exceptional integer. The original two-dimensional characteristic-zero association, remaining local/image/regularity inputs, automorphy and literal higher continuation remain. No acceptance gate is closed. 16/20; DUB-17--20 OPEN.',externalBuild=False,externalImport=False,rootPinsChanged=False,proofLimitsChanged=False)
rf='source-gamma-one-quotient-character-audit-route-1461.json';write(rf,json.dumps(route,indent=2)+'\n')
c=(s/'record_gamma_one_transfer_1447.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-diamond-transfer-audit-route-1447',rf[:-5]),('source-gamma-one-diamond-transfer-1',stem),(old,new),('ScratchOwnership1447','ScratchOwnership1461'),('GAMMA ONE DIAMOND TRANSFER','GAMMA ONE QUOTIENT CHARACTER')]:c=c.replace(a,b)
c=c.replace('(4, 10, 22)','(10, 13, 32)').replace('queries=10','queries=13').replace('modules=4','modules=10').replace('linterScopes=4','linterScopes=10')
c=c.replace("text.count('with 16 linters') == 4","text.count('with 16 linters') == 10").replace('all 22 required','all 32 required').replace('requiredProofValueEdges=22','requiredProofValueEdges=32').replace('proofEdges=22','proofEdges=32')
ast.parse(c);write('record_gamma_one_quotient_character_1461.py',c)
c=(s/'audit_gamma_one_transfer_1447.ps1').read_text(encoding='utf-8-sig')
for a,b in [(old,new),('ScratchOwnership1447','ScratchOwnership1461'),('record_gamma_one_transfer_1447','record_gamma_one_quotient_character_1461')]:c=c.replace(a,b)
write('audit_gamma_one_quotient_character_1461.ps1',c)
print(json.dumps(dict(modules=len(mods),queries=len(cfg['queries']),proofEdges=len(edges))))
