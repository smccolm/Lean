from pathlib import Path
import re
p=Path(r'E:\Lean\.tmp\dubon83')
prod=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
G=chr(915); Z=chr(8484); N=chr(8469)
def adapt(name):
 s=(prod/(name+'.lean')).read_text(encoding='utf-8');s=s[s.index('namespace Dubon2026'):]
 s=s.replace('Dubon2026.SourceFunctionField','Dubon2026.SourceFunctionField.GammaOne').replace('originalArithmetic','arithmetic')
 s=s.replace('modularFunctionFieldOver N L','functionFieldOver GAMMA L').replace('variable (N : '+N+')','variable (GAMMA : Subgroup (Matrix.SpecialLinearGroup (Fin 2) '+Z+'))')
 return re.sub(r'\bN\b','GAMMA',s).replace('GAMMA',G)
s=adapt('SourceOriginalArithmeticDivisors')
s=s.replace('[NeZero '+G+'] [IsAlgClosed L]','['+G+'.FiniteIndex] [IsAlgClosed L]\n    (hT : ModularGroup.T '+chr(8712)+' '+G+')')
s=s.replace('original_place_residue_algebraMap_bijective '+G+' L v','functionFieldOver_residue_bijective '+G+' hT v')
header='''import SourceGammaOneArithmeticPlaces
import Dubon2026.SourceCurveDivisorDegree
import Dubon2026.SourceCurveFiniteCoordinateResidues

/-! DUB-17/18 -> original all-weight adic association -> arithmetic Gamma1
realization -> genuine arithmetic Picard action. Existing finite-coordinate
closed residues and the actual place permutation prove preservation of
degree and principal divisors. Both Gamma1 and its Hecke subgroup satisfy
the translation/finite-index conditions in the final consumer. -/
'''
lemma='''theorem functionFieldOver_residue_bijective [GAMMA.FiniteIndex] [IsAlgClosed L]
    (hT : ModularGroup.T IN GAMMA) (v : Place L F) :
    Function.Bijective (algebraMap L v.ResidueField) := by
  haveI := finiteDimensional_jCoordinateOver hT L
  exact place_residue_bijective_of_finite_coordinate (jCoordinateOver GAMMA L) v

'''.replace('GAMMA',G).replace(' IN ',' '+chr(8712)+' ')
i=s.index('/-- Pushforward');s=s[:i]+lemma+s[i:]
f=p/'SourceGammaOneArithmeticDivisors.lean';assert not f.exists();f.write_text(header+s,encoding='utf-8')
s=adapt('SourceOriginalArithmeticPicard')
s=s.replace('variable [NeZero '+G+'] [IsAlgClosed L]','variable ['+G+'.FiniteIndex] [IsAlgClosed L] (hT : ModularGroup.T '+chr(8712)+' '+G+')')
s=s.replace('rw [arithmeticDivisor_degree]','rw [arithmeticDivisor_degree '+G+' hT]')
for name in ['arithmeticDegZero','arithmeticPicard','arithmeticPicard_mk']:
 s=s.replace(name+' '+G+' ',name+' '+G+' hT ')
header='''import SourceGammaOneArithmeticDivisors

/-! DUB-17/18 -> original all-weight adic association -> arithmetic Gamma1
realization -> actual arithmetic action on degree-zero divisor classes.
The same coefficient action preserves the proved geometric relations.
Reuse native quotient functoriality and the original place-action laws.
Hecke naturality is a separate consumer; no Galois association is claimed. -/
'''
f=p/'SourceGammaOneArithmeticPicard.lean';assert not f.exists();f.write_text(header+s,encoding='utf-8')
print('Prepared actual arithmetic divisor/Picard adaptations; no compile or audit claim.')
