from pathlib import Path
from datetime import datetime, timezone
import ast, json, re, hashlib

p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026')
mods=['SourceGammaOneDiamondPeriodInclusion','SourceGammaOneBinaryDiamondTateH1',
 'SourceCyclotomicDiamondCovariance','SourceRationalDiamondFraction',
 'SourceRationalCuspDiamondImage','SourceRationalModularCuspQuotient',
 'SourceRationalDiamondQuotientGerm','SourceRationalDiamondCoefficients',
 'SourceGammaOneDiamondRationalGenerators','SourceGammaOneDiamondComplexArithmetic',
 'SourceGammaOneArithmeticDiamondGenerators','SourceGammaOneArithmeticDiamondGalois',
 'SourceGammaOneDiamondGaloisPicard']
attempts=['1221a','1222a','1223b','1224a','1225a','1226b','1227a','1228b',
 '1229b','1230b','1231a','1232a','1233a']
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
edges=ths+defs+['Dubon2026.SourceFunctionField.GammaOne.'+x for x in [
 'arithmeticPicardTatePeriodTensorEquiv_diamond','binaryLatticeH1Equiv_diamond',
 'diamondFieldHom_ratio','ConstantField.fieldMap_arithmeticDiamondHom',
 'arithmeticDiamondPicard_mk','arithmeticPicard_mk']]
edges += ['Dubon2026.SourceFricke.'+x for x in [
 'exists_modular_cyclotomic_conjugate','CyclotomicConjugates.modular',
 'exists_cyclotomic_aut_exponent','exists_field_laurent_holomorphic_fraction',
 'gammaOne_cuspWeightImage_mem_original_of_rational_series',
 'exists_rational_cuspWeightImage_laurent']]
prior=json.loads((p/'source-diamond-picard-periods-1-audit-config.json').read_text())
cfg=dict(modules=mods,theorems=ths,constructions=defs,queries=ths+defs,roots=ths+defs,
 proofEdges=edges,localModules=mods+prior['localModules'],separatelyAxiomChecked=[],compileEvidence=ev)
def write(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
stem='source-diamond-galois-1'
write(stem+'-audit-config.json',json.dumps(cfg,indent=2)+'\n')
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
old='SourceDiamondPicardPeriods';new='SourceDiamondGalois'
for a,b in [('Audit1','Audit1'),('DependencyAudit1','DependencyAudit1'),('ScratchOwnership1220','ScratchOwnership1234')]:
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
  s=s[:start]+' occur in the original arithmetic diamond Tate/H1 transpose, cyclotomic covariance and rational descent, actual integral modular-ratio generators, original field Galois commutation, and original place/Picard/Tate Galois compatibility. The original homogeneous normalizer convention, parabolic transfer and exceptional primes, association and higher continuation remain unresolved'+s[end:]
 else:
  s=re.sub(r'let mods : Array Name := #\[[^\n]*\]','let mods : Array Name := '+arr(mods),s)
 s=s.replace('DIAMOND PICARD PERIODS','DIAMOND GALOIS')
 write(new+b+'.lean',s)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
reuse=[p/'source-diamond-picard-periods-1-scratch-receipt.json',
 p/'source-gamma-one-arithmetic-diamond-1-scratch-receipt.json']
reuse += [r/'Extension/Dubon2026'/(m+'.lean') for m in [
 'SourceCyclotomicFractionCovariance','SourceCyclotomicTraceStructure',
 'SourceRationalCuspWeightIntegrality','SourceGammaOneAllModularRatioMembership',
 'SourceGammaOneArithmeticField','SourceGammaOneHeckeArithmetic',
 'SourceGammaOneBinaryTateH1','SourceGammaOneArithmeticPeriodInclusion']]
route=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),
 chain='DUB17 Theorem 2.6 / DUB18 Corollary 8.2 -> literal higher symmetric-power continuation -> arithmetic automorphy -> original all-weight association -> original finite Gamma1 homogeneous-coefficient arithmetic realization -> original arithmetic diamond Galois compatibility and Tate/H1 comparison.',
 reuseChecked=[dict(path=str(f),sha256=sha(f)) for f in reuse],
 shorterRoute='Reuse the existing cyclotomic Fricke conjugation and fixed-field theorem. The conjugate Gamma0 lift has the same diamond label; Gamma1 invariance makes its pullback identical. Existing discriminant normalization converts original same-weight rational modular ratios to rational cusp quotients, proving diamond coefficients rational. Original field generation then proves Galois commutation, with no automorphism extension to C. Existing places, Picard quotients and Tate maps propagate that equality. Existing arithmetic period inclusion composes with the native homogeneous-valued H1 diamond comparison.',
 assumptionsToDischarge=[
 'The actual arithmetic Picard Tate diamond transposes to the original homogeneous-valued finite Gamma1 H1 diamond, with its coefficient endomorphism explicit.',
 'Cyclotomic covariance and rational fixed-field descent apply to actual original integral modular-ratio generators; no rationality, fraction membership or cusp-germ assumptions remain.',
 'The actual diamond on both the complex and original algebraic-closure function fields commutes with the original coefficient Galois action.',
 'The original arithmetic place, divisor, Picard and Tate diamond commute with Galois, for every Tate prime without additional restrictions.'],
 remaining='Supersedes historical missing diamond Galois compatibility in scopes 1204/1212/1220. The original homogeneous normalizer coefficient convention, parabolic transfer preimages, exceptional primes, Frobenius/inertia, characteristic-zero all-weight association and higher continuation remain. 16/20; DUB17--20 OPEN.',
 preservedFailures='1223a finite residue simplification, 1226a Laurent coercion and unused simp, 1228a unreduced lambda rewrite; sources/logs retained. Successful 1229a and 1230a sources retained before exposing the coefficient lemma and rebuilding its consumer. No proof limits or standards changed.',
 externalBuild=False,externalImport=False,rootPinsChanged=False)
write('source-diamond-galois-audit-route-1234.json',json.dumps(route,indent=2)+'\n')
s=(p/'record_diamond_picard_periods_1220.py').read_text(encoding='utf-8')
for a,b in [('source-diamond-picard-periods-audit-route-1220','source-diamond-galois-audit-route-1234'),
 ('source-diamond-picard-periods-1',stem),(old,new),('ScratchOwnership1220','ScratchOwnership1234'),
 ('DIAMOND PICARD PERIODS','DIAMOND GALOIS')]:s=s.replace(a,b)
s=s.replace('(7, 19, 35)',str((len(mods),len(ths+defs),len(edges))))
s=s.replace('== 7','== 13').replace('linterScopes=7','linterScopes=13').replace('modules=7','modules=13')
s=s.replace('all 35 required',f'all {len(edges)} required').replace('requiredProofValueEdges=35',f'requiredProofValueEdges={len(edges)}')
s=s.replace('proofEdges=35',f'proofEdges={len(edges)}').replace('queries=19',f'queries={len(ths+defs)}')
ast.parse(s);write('record_diamond_galois_1234.py',s)
s=(p/'audit_diamond_picard_periods_1220.ps1').read_text(encoding='utf-8')
for a,b in [(old,new),('ScratchOwnership1220','ScratchOwnership1234'),('record_diamond_picard_periods_1220','record_diamond_galois_1234')]:s=s.replace(a,b)
write('audit_diamond_galois_1234.ps1',s)
print(json.dumps(dict(modules=len(mods),theorems=len(ths),constructions=len(defs),queries=len(ths+defs),edges=len(edges))))
