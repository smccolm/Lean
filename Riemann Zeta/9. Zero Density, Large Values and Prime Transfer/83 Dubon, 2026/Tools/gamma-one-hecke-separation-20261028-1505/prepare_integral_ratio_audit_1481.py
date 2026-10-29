from pathlib import Path
from datetime import datetime,timezone
import ast,hashlib,json,re
s=Path(__file__).parent
versions=json.loads((s/'gamma-one-integral-ratio-versions-1480.json').read_text(encoding='utf-8'))
mods=list(versions);ths=[];defs=[]
for m in mods:
 code=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',(s/(m+'.lean')).read_text(encoding='utf-8'),flags=re.S))
 ns=re.search(r'^namespace (\S+)',code,re.M)[1]+'.'
 ths += [ns+x for x in re.findall(r'^theorem\s+([\w.\x27]+)',code,re.M)]
 defs += [ns+x for x in re.findall(r'^(?:def|instance)\s+([\w.\x27]+)',code,re.M)]
gn='Dubon2026.SourceFunctionField.GammaOne.';cr=gn+'CoefficientReduction.';ff='Dubon2026.SourceFunctionField.'
roots=[cr+'gammaOne_degree_and_residueField_of_integral_ratio_index',cr+'integral_ratio_coordinate_degree_le_original']
edges=ths+[gn+'functionFieldOver_eq_qExpFunctionFieldC',gn+'div_mem_qExpFunctionFieldC',cr+'resHom_mem_residueImage',cr+'resHom_eq',cr+'finite_residueCoordinate_and_degree_le',gn+'coordinate_finrank_eq_relfinrank',gn+'gammaOne_coordinate_relfinrank_eq_index',ff+'dedekindEtaUnit_mul_inv',ff+'qExpansion_E4_eq_map_eisenstein4',ff+'qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit','IntermediateField.relfinrank_mul_relfinrank','IntermediateField.relfinrank_eq_one_iff',ff+'GaussReduction.ι_eq_zero_iff']
assert (len(mods),len(ths),len(defs),len(edges))==(4,7,0,20)
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths,roots=roots,proofEdges=edges,localModules=mods,separatelyAxiomChecked=[],compileEvidence={m:m+'-1480' for m in mods})
def write(n,c):
 t=s/n;assert not t.exists(),t;t.write_text(c,encoding='utf-8')
stem='source-gamma-one-integral-ratio-1';write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
old,new='SourceGammaOneQuotientCharacter','SourceGammaOneIntegralRatio'
for a,b in [('Audit1','Audit1'),('DependencyAudit1','DependencyAudit1'),('ScratchOwnership1461','ScratchOwnership1481')]:
 c=(s/(old+a+'.lean')).read_text(encoding='utf-8')
 c='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+c[c.index('\nopen Lean'):]
 if a=='Audit1':
  c=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in cfg['queries']),c,count=1)
  for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:c=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),c)
  c=re.sub(r'#lint in [^\n]+\n','',c).rstrip()+'\n\n'+''.join('#lint in '+m+'\n' for m in mods)
 elif a=='DependencyAudit1':
  for k,v in [('roots',roots),('localModules',mods),('required',edges)]:c=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),c)
  start=c.index(' occur in the ');end=c.index('; DUB17--20 OPEN.',start)
  c=c[:start]+' occur in the proof value closure of the actual integral-ratio inclusion, literal j membership, residue degree comparison and the native original degree/field equality consumer. The exact signed-index lower bound remains an explicit upstream obligation; genus and parabolic transfer remain open'+c[end:]
 else:c=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),c)
 c=c.replace('GAMMA ONE QUOTIENT CHARACTER','GAMMA ONE INTEGRAL RATIO')
 write(new+b+'.lean',c)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
src=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
reuse=[src/(n+'.lean') for n in ['SourceGammaOneGaussResidueImage','SourceGammaOneGaussResidueHom','SourceGammaOneScalarExtension','SourceGammaOneJCoordinate','SourceGammaOneResidueCoordinateFinite','SourceGammaOneHeckeCoordinateDegree']]+[s/'targeted-reuse-review-1471.json',s/'Dubon Targeted Reuse Review 2026-10-28.md']
chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher symmetric-power continuation -> automorphy -> original all-weight characteristic-zero association -> original Gamma1 Tate/Frobenius arithmetic realization -> exact coordinate-degree and genus preservation -> original integral-ratio and actual residue-field comparison.'
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain=chain,reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],shorterRoute='The complete upstream Sol subtree exposed an integral Eisenstein coset separation route to the signed-index lower bound. Reuse the native scalar-extension identity, Gauss residue construction, j/E4/discriminant normalization, finite residue upper bound and original signed-index degree. The new comparison identifies the actual residue object without assuming a good-reduction model. No further Fricke integrality or general GammaH infrastructure is developed in this scope.',assumptionsToDischarge=['Every residue-characteristic integral modular-form ratio belongs to the actual native residue image.','The original j belongs to that integral-ratio field in every residue characteristic.','Its coordinate degree is bounded by the actual residue degree and then by the original characteristic-zero degree.','The precise external signed-index lower bound implies native degree preservation and equality of the actual residue image with the residue integral-ratio field.'],remaining='The signed-index lower bound is not yet proved natively; its integral Eisenstein and integral-slash route is being adapted. Genus preservation, exact integral parabolic transfer, the required two-dimensional characteristic-zero realization, remaining local/image/regularity inputs, automorphy and literal higher continuation remain. Acceptance stays 16/20; DUB-17--20 OPEN.',externalBuild=False,externalImport=False,rootPinsChanged=False,proofLimitsChanged=False)
rf='source-gamma-one-integral-ratio-audit-route-1481.json';write(rf,json.dumps(route,indent=2)+'\n')
c=(s/'record_gamma_one_quotient_character_1461.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-quotient-character-audit-route-1461',rf[:-5]),('source-gamma-one-quotient-character-1',stem),(old,new),('ScratchOwnership1461','ScratchOwnership1481'),('GAMMA ONE QUOTIENT CHARACTER','GAMMA ONE INTEGRAL RATIO')]:c=c.replace(a,b)
c=c.replace('(10, 13, 32)','(4, 7, 20)').replace('queries=13','queries=7').replace('modules=10','modules=4').replace('linterScopes=10','linterScopes=4')
c=c.replace("text.count('with 16 linters') == 10","text.count('with 16 linters') == 4").replace('all 32 required','all 20 required').replace('requiredProofValueEdges=32','requiredProofValueEdges=20').replace('proofEdges=32','proofEdges=20')
ast.parse(c);write('record_gamma_one_integral_ratio_1481.py',c)
c=(s/'audit_gamma_one_quotient_character_1461.ps1').read_text(encoding='utf-8-sig')
for a,b in [(old,new),('ScratchOwnership1461','ScratchOwnership1481'),('record_gamma_one_quotient_character_1461','record_gamma_one_integral_ratio_1481')]:c=c.replace(a,b)
write('audit_gamma_one_integral_ratio_1481.ps1',c)
print(json.dumps(dict(modules=len(mods),queries=len(cfg['queries']),proofEdges=len(edges))))
