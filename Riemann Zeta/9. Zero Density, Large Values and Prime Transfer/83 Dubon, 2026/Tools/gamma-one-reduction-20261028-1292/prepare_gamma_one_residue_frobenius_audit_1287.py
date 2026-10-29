from pathlib import Path
from datetime import datetime,timezone
import ast,hashlib,json,re
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
mods=['SourceGammaOneResidueFrobenius']
cn='Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction.'
ths=[];defs=[]
for m in mods:
 assert (p/(m+'1286d.exit')).read_text().strip()=='0'
 assert (p/(m+'1286d.log')).stat().st_size==0
 code=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',(p/(m+'.lean')).read_text(encoding='utf-8'),flags=re.S))
 ths += [cn+x for x in re.findall(r"^theorem\s+([\w.']+)",code,re.M)]
 defs += [cn+x for x in re.findall(r"^def\s+([\w.']+)",code,re.M)]
roots=[cn+x for x in ['geometricFrobenius_isIntegral','geometricFrobenius_finite',
 'residueHeckeBeta_eq_alpha_geometricFrobenius']]
edges=ths+defs+[cn+x for x in ['decompositionResidueAut',
 'finite_residueCoordinate_and_degree_le','transcendental_residueJCoordinate',
 'residueHeckeAlpha','residueHeckeBeta']]+[
 'Dubon2026.SourceCurve.finite_over_transcendental_of_finite_coordinate',
 'Dubon2026.SourceCurve.finite_hom_of_finite_image_coordinate']
prev=json.loads((p/'source-gamma-one-residue-compatibility-1-audit-config.json').read_text(encoding='utf-8'))
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,roots=roots,
 proofEdges=edges,localModules=prev['localModules']+mods,separatelyAxiomChecked=[],
 compileEvidence={m:m+'1286d' for m in mods})
assert(len(ths),len(defs),len(edges))==(8,1,16)
def write(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
stem='source-gamma-one-residue-frobenius-1'
write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
old='SourceGammaOneResidueCompatibility';new='SourceGammaOneResidueFrobenius'
for a,b in [('Audit1','Audit1'),('DependencyAudit1','DependencyAudit1'),
 ('ScratchOwnership1285','ScratchOwnership1287')]:
 s=(p/(old+a+'.lean')).read_text(encoding='utf-8')
 s='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+s[s.index('\nopen Lean'):]
 if a=='Audit1':
  s=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in cfg['queries']),s,count=1)
  for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:
   s=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),s)
  s=re.sub(r'#lint in [^\n]+\n','',s).rstrip()+'\n\n'+''.join('#lint in '+m+'\n' for m in mods)
 elif a=='DependencyAudit1':
  for k,v in [('roots',roots),('localModules',cfg['localModules']),('required',edges)]:
   s=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),s)
  start=s.index(' occur in the ');end=s.index('; DUB17--20 OPEN.',start)
  s=s[:start]+' occur in the proof value closures of the actual Gamma1 residue geometric Frobenius integrality, finiteness and original Hecke beta factorization. Norm reduction, degree and genus preservation, Picard specialization and the geometric Tate quadratic remain unresolved'+s[end:]
 else:
  s=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),s)
 s=s.replace('GAMMA ONE RESIDUE COMPATIBILITY','GAMMA ONE RESIDUE FROBENIUS')
 write(new+b+'.lean',s)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
reuse=[r/'Extension/Dubon2026'/(m+'.lean') for m in ['SourceLaurentFrobenius',
 'SourceResidueGeometricFrobenius','SourceFiniteCoordinateHom','SourceCurveFiniteCoordinateResidues']]
reuse += [p/'source-gamma-one-residue-compatibility-1-scratch-receipt.json',
 r.parents[1]/'.lake/packages/mathlib/Mathlib/FieldTheory/IntermediateField/Basic.lean']
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),
 chain='DUB17 Theorem 2.6 / DUB18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight characteristic-zero association -> original Gamma1 Picard/Tate Frobenius -> actual residue Hecke correspondence -> geometric Frobenius factorization.',
 reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],
 shorterRoute='Reuse the native Laurent Frobenius identity, actual decomposition residue automorphism, native finite-coordinate exchange and Mathlib coe_inclusion. Inverse coefficient action followed by the absolute pth power gives the actual constant-linear q-substitution on the original residue image. The explicit monic polynomial proves integrality; the native finite-coordinate theorem proves finiteness. The second original residue Hecke map is the first map after this Frobenius. Named Mathlib inclusion evaluation avoids kernel normalization of the concrete intermediate-field record without increasing limits.',
 assumptionsToDischarge=[
 'For a decomposition element whose action on residue constants is pth power, the original residue image has a constant-linear geometric Frobenius with literal q to q^p Laurent action.',
 'The actual endomorphism is integral, and finite for a finite-index original subgroup containing T.',
 'The actual Gamma1 residue Hecke beta map factors through this endomorphism and the actual alpha inclusion.'],
 remaining='The arithmetic Frobenius constant-action premise is explicit. No original norm identity, degree equality, genus preservation, place/Picard specialization or prime-to-residue torsion injectivity is proved by this module. The original geometric Tate quadratic, inertia on original Picard torsion, parabolic character realization, exceptional primes, coefficient-field realization, original all-weight characteristic-zero association, automorphy and literal higher continuation remain. 16/20; DUB17--20 OPEN.',
 externalBuild=False,externalImport=False,rootPinsChanged=False)
routefile='source-gamma-one-residue-frobenius-audit-route-1287.json'
write(routefile,json.dumps(route,indent=2)+'\n')
s=(p/'record_gamma_one_residue_compatibility_1285.py').read_text(encoding='utf-8')
for a,b in [('source-gamma-one-residue-compatibility-audit-route-1285',routefile[:-5]),
 ('source-gamma-one-residue-compatibility-1',stem),(old,new),
 ('ScratchOwnership1285','ScratchOwnership1287'),
 ('GAMMA ONE RESIDUE COMPATIBILITY','GAMMA ONE RESIDUE FROBENIUS')]:s=s.replace(a,b)
s=s.replace('(6, 28, 39)','(1, 9, 16)').replace('== 6','== 1')
s=s.replace('linterScopes=6','linterScopes=1').replace('modules=6','modules=1')
s=s.replace('all 39 required','all 16 required').replace('requiredProofValueEdges=39','requiredProofValueEdges=16')
s=s.replace('proofEdges=39','proofEdges=16').replace('queries=28','queries=9')
ast.parse(s);write('record_gamma_one_residue_frobenius_1287.py',s)
s=(p/'audit_gamma_one_residue_compatibility_1285.ps1').read_text(encoding='utf-8')
for a,b in [(old,new),('ScratchOwnership1285','ScratchOwnership1287'),
 ('record_gamma_one_residue_compatibility_1285','record_gamma_one_residue_frobenius_1287')]:s=s.replace(a,b)
write('audit_gamma_one_residue_frobenius_1287.ps1',s)
print(json.dumps(dict(modules=1,queries=9,edges=16)))
