from pathlib import Path
from datetime import datetime,timezone
import ast,hashlib,json,re
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
mods=['SourceGammaOneResidueSeparability','SourceGammaOneDecompositionGauss',
 'SourceGammaOneResidueArithmetic','SourceGammaOneHeckeGauss','SourceGammaOneResidueHecke',
 'SourceGammaOneResidueHeckeFinite']
attempts=['1279b','1280a','1280a','1281b','1281b','1282a']
ev={m:m+a for m,a in zip(mods,attempts)}
ths=[];defs=[]
for m in mods:
 assert (p/(ev[m]+'.exit')).read_text().strip()=='0'
 assert (p/(ev[m]+'.log')).stat().st_size==0
 raw=(p/(m+'.lean')).read_text(encoding='utf-8')
 code=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',raw,flags=re.S))
 ns=re.findall(r'^namespace ([\w.]+)',code,re.M);assert len(ns)==1
 ths += [ns[0]+'.'+x for x in re.findall(r"^theorem\s+([\w.']+)",code,re.M)]
 defs += [ns[0]+'.'+x for x in re.findall(r"^def\s+([\w.']+)",code,re.M)]
gn='Dubon2026.SourceFunctionField.GammaOne.';cn=gn+'CoefficientReduction.'
roots=[cn+x for x in ['gammaOne_isSeparable_residueCoordinate',
 'residueToImage_arithmetic_inertia','residueToImage_arithmetic_frobenius_coeff',
 'residueHeckeAlpha_reduction','residueHeckeBeta_reduction',
 'residueHeckeAlpha_finite','residueHeckeBeta_finite']]
edges=[cn+x for x in ['pow_ne_residueJCoordinate','isSeparable_residueCoordinate',
 'gammaOne_isSeparable_residueCoordinate','decompositionGaussHom',
 'decompositionGaussHom_resHom','coeffMap_decomposition_mem_residueImage',
 'decompositionResidueAut','decompositionGaussHom_residueToImage',
 'decompositionResidueAut_eq_one_of_inertia','residueToImage_arithmetic_inertia',
 'residueToImage_arithmetic_frobenius_coeff','heckeAlpha_mem_gaussRing',
 'heckeAlphaGauss','heckeAlphaGauss_resHom','isInt_qExpand','heckeBeta_mem_gaussRing',
 'heckeBetaGauss','heckeBetaGauss_resHom','residueImage_heckeAlpha_le','residueHeckeAlpha',
 'residueHeckeAlpha_reduction','qExpand_mem_residueImage','residueHeckeBeta',
 'residueHeckeBeta_reduction','residue_hecke_hom_finite','residueHeckeAlpha_finite',
 'residueHeckeBeta_finite','finite_residueCoordinate_and_degree_le',
 'transcendental_residueJCoordinate','residueToImage_surjective']]
edges += [gn+x for x in ['arithmeticRingAut','heckeAlpha','heckeBeta']]
edges += ['Dubon2026.SourceFunctionField.GaussReduction.isInt_coeffMap_decomposition',
 'Dubon2026.SourceFunctionField.GaussReduction.coeffMap_residue_decomposition',
 'Dubon2026.SourceFunctionField.pow_ne_jqModC',
 'Dubon2026.SourceCurve.isSeparable_of_forall_pow_ne',
 'Dubon2026.SourceCurve.finite_over_transcendental_of_finite_coordinate',
 'Dubon2026.SourceCurve.finite_hom_of_finite_image_coordinate']
prev=json.loads((p/'source-gamma-one-reduction-2-audit-config.json').read_text(encoding='utf-8'))
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,
 roots=roots,proofEdges=edges,localModules=prev['modules']+mods,
 separatelyAxiomChecked=[],compileEvidence=ev)
def write(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
stem='source-gamma-one-residue-compatibility-1'
write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
old='SourceGammaOneReduction';new='SourceGammaOneResidueCompatibility'
for a,b in [('Audit2','Audit1'),('DependencyAudit2','DependencyAudit1'),('ScratchOwnership1278b','ScratchOwnership1285')]:
 s=(p/(old+a+'.lean')).read_text(encoding='utf-8')
 s='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+s[s.index('\nopen Lean'):]
 if a=='Audit2':
  s=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in cfg['queries']),s,count=1)
  for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:
   s=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),s)
  s=re.sub(r'#lint in [^\n]+\n','',s).rstrip()+'\n\n'+''.join('#lint in '+m+'\n' for m in mods)
 elif a=='DependencyAudit2':
  for k,v in [('roots',roots),('localModules',cfg['localModules']),('required',edges)]:
   s=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),s)
  start=s.index(' occur in the ');end=s.index('; DUB17--20 OPEN.',start)
  s=s[:start]+' occur in the proof value closures of the original Gamma1 separating-coordinate, arithmetic inertia/Frobenius coefficient reduction, and finite original Hecke residue-map endpoints. The original field maps, literal residue image and native finite-coordinate exchange are consumed. Degree equality, genus preservation, place and Picard specialization, torsion injectivity and the geometric Frobenius quadratic remain unresolved'+s[end:]
 else:s=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),s)
 s=s.replace('GAMMA ONE REDUCTION','GAMMA ONE RESIDUE COMPATIBILITY')
 write(new+b+'.lean',s)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
reuse=[r/'Extension/Dubon2026'/(m+'.lean') for m in ['SourceModularCoordinateNotPower',
 'SourcePerfectSeparatingCoordinate','SourceDecompositionGaussAction',
 'SourceOriginalInertiaIntegralFunctions','SourceGammaOneArithmeticField',
 'SourceGammaOneHeckeDegeneracy','SourceGammaOneHeckeFieldFinite',
 'SourceFiniteCoordinateHom','SourceCurveFiniteCoordinateResidues']]
reuse.append(p/'source-gamma-one-reduction-2-scratch-receipt.json')
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),
 chain='DUB17 Theorem 2.6 / DUB18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> original finite Gamma1 arithmetic realization -> original geometric Tate Frobenius/inertia -> equivariant original good reduction, finite residue Hecke correspondence and Picard torsion specialization.',
 reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],
 shorterRoute='The native simple pole of j rules out pth powers, and the existing perfect-constant criterion proves separability. The native decomposition action on integral fractions restricts the existing original Gamma1 arithmetic automorphism. Surjectivity of the actual residue image constructs its genuine coefficient action; native inertia membership makes this action trivial. Both original Hecke field maps preserve the same valuation; native coefficient/substitution commutation gives their literal reductions. Reuse the existing coordinate-exchange and finite-hom theorems to prove both residue maps finite. Explicit named preservation lemmas and Mathlib codRestrict avoid kernel normalization of a large concrete ring-map record. No proof limit is changed.',
 assumptionsToDischarge=[
 'The actual original Gamma1 residue j-coordinate separates the finite residue function field over perfect constants; its no-pth-power condition is proved from the literal Laurent pole.',
 'The original arithmetic decomposition action preserves the constructed valuation. Literal reduction is equivariant; inertia fixes its actual residue image, and arithmetic Frobenius reduces by raising coefficients to the residue characteristic power.',
 'Both original Gamma1 Hecke maps restrict to the constructed valuation and induce the actual inclusion and q-substitution on residue fields, with exact reduction compatibility. Both residue field maps are proved finite using original finite-coordinate inputs.'],
 remaining='Function-level arithmetic/Hecke reduction and finite residue maps do not prove degree equality, genus preservation, place/Picard specialization, prime-to-residue torsion injectivity, or the two geometric Frobenius components. The original geometric Tate quadratic and inertia on original Picard torsion, parabolic character realization, exceptional primes, coefficient-field realization, original all-weight characteristic-zero association, automorphy and literal higher continuation remain. 16/20; DUB17--20 OPEN.',
 preservedFailures='Original kernel-timeout and unused-instance diagnostics are retained with inert failed source. The successor replaces concrete ring-map record normalization by native codRestrict and explicit preservation proofs; the unused Algebra assumption is omitted only for the pure Laurent substitution lemma. No mathematical statement was weakened.',
 externalBuild=False,externalImport=False,rootPinsChanged=False)
write('source-gamma-one-residue-compatibility-audit-route-1285.json',json.dumps(route,indent=2)+'\n')
s=(p/'record_gamma_one_reduction_1278b.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-reduction-audit-route-1278b','source-gamma-one-residue-compatibility-audit-route-1285'),
 ('source-gamma-one-reduction-2',stem),(old,new),('Audit2','Audit1'),
 ('ScratchOwnership1278b','ScratchOwnership1285'),('GAMMA ONE REDUCTION','GAMMA ONE RESIDUE COMPATIBILITY')]:s=s.replace(a,b)
s=s.replace('(10, 40, 23)',str((len(mods),len(ths+defs),len(edges))))
s=s.replace('== 10','== 6').replace('linterScopes=10','linterScopes=6').replace('modules=10','modules=6')
s=s.replace('all 23 required',f'all {len(edges)} required').replace('requiredProofValueEdges=23',f'requiredProofValueEdges={len(edges)}')
s=s.replace('proofEdges=23',f'proofEdges={len(edges)}').replace('queries=40',f'queries={len(ths+defs)}')
ast.parse(s);write('record_gamma_one_residue_compatibility_1285.py',s)
s=(p/'audit_gamma_one_reduction_1278b.ps1').read_text(encoding='utf-8')
for a,b in [(old,new),('Audit2','Audit1'),('ScratchOwnership1278b','ScratchOwnership1285'),
 ('record_gamma_one_reduction_1278b','record_gamma_one_residue_compatibility_1285')]:s=s.replace(a,b)
write('audit_gamma_one_residue_compatibility_1285.ps1',s)
print(json.dumps(dict(modules=len(mods),theorems=len(ths),constructions=len(defs),queries=len(ths+defs),edges=len(edges))))
