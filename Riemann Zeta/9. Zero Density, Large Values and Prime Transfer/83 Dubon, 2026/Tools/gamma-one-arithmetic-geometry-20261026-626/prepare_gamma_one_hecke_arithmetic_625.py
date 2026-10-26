from pathlib import Path
import re
p=Path(r'E:\Lean\.tmp\dubon83')
prod=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
G=chr(915); D=chr(916); Z=chr(8484); N=chr(8469)
def adapt(name):
 s=(prod/(name+'.lean')).read_text(encoding='utf-8');s=s[s.index('namespace Dubon2026'):]
 s=s.replace('Dubon2026.SourceFunctionField','Dubon2026.SourceFunctionField.GammaOne').replace('originalArithmetic','arithmetic').replace('original_finitePullbackAlong','finitePullbackAlong').replace('original_geometricPushforwardAlong','geometricPushforwardAlong')
 s=s.replace('modularFunctionFieldOver N L','functionFieldOver GAMMA L').replace('modularFunctionFieldOver M L','functionFieldOver DELTA L')
 s=s.replace('(N M : '+N+')','(GAMMA DELTA : Subgroup (Matrix.SpecialLinearGroup (Fin 2) '+Z+'))').replace('(N : '+N+')','(GAMMA : Subgroup (Matrix.SpecialLinearGroup (Fin 2) '+Z+'))')
 return re.sub(r'\bM\b','DELTA',re.sub(r'\bN\b','GAMMA',s)).replace('GAMMA',G).replace('DELTA',D)
for old,new,imports,comment in [
 ('SourceOriginalHeckeArithmeticPlaces','SourceGammaOneHeckeArithmeticPlaces','import Dubon2026.SourceCurveCorrespondencePlaces\nimport SourceGammaOneArithmeticDivisors\n','Commutation of the actual field maps gives place-restriction compatibility. Existing discrete orders then prove the actual ramification invariance.'),
 ('SourceOriginalHeckeArithmeticDivisors','SourceGammaOneHeckeArithmeticDivisors','import SourceGammaOneHeckeArithmeticPlaces\nimport SourceGammaOneHeckePicard\nimport SourceGammaOneArithmeticPicard\n','The proved place-restriction and ramification equations make actual divisor pullback and pushforward commute with coefficient action. The final Gamma1 consumer derives field commutation for both literal maps.')]:
 header=imports+'\n/-! DUB-17/18 -> original all-weight adic association -> arithmetic Gamma1\nrealization -> arithmetic equivariance of the actual Picard Hecke operator.\n'+comment+'\nReuse the existing original arithmetic correspondence proof on these actual\nintegral-ratio fields. No arithmetic naturality certificate is postulated. -/\n'
 f=p/(new+'.lean');assert not f.exists();f.write_text(header+adapt(old),encoding='utf-8')
print('Prepared actual place/divisor naturality adaptations; compilation pending.')
