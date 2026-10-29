from pathlib import Path
p=Path(__file__).parent
r=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
s=(r/'SourceOriginalPicardFieldOfDefinition.lean').read_text(encoding='utf-8')
s=s.replace('import Dubon2026.SourceOriginalPlaceFieldOfDefinition','import SourceGammaOnePlaceFieldDefinition1415a').replace('import Dubon2026.SourceOriginalArithmeticPicard','import Dubon2026.SourceGammaOneArithmeticTateOperators')
start=s.index('/-!');end=s.index('-/',start)+2
s=s[:start]+'''/-! DUB-17/18 -> original all-weight arithmetic association -> continuous
finite homogeneous-valued Tate action -> open stabilizers on actual Gamma1
Picard classes. Reuse the original finite-support argument with the proved
finite fields of definition of the literal Gamma1 places. This constructs
the finite field fixing each actual divisor class, without a continuity
or finite-image premise. -/'''+s[end:]
s=s.replace('namespace Dubon2026.SourceFunctionField','namespace Dubon2026.SourceFunctionField.GammaOne').replace('end Dubon2026.SourceFunctionField','end Dubon2026.SourceFunctionField.GammaOne').replace('open SourceCurve','open SourceCurve CongruenceSubgroup')
s=s.replace('local notation "Qbar" => AlgebraicClosure ℚ','local notation "Qbar" => AlgebraicClosure ℚ\nlocal notation "J" N => Pic0 Qbar (functionFieldOver (Gamma1 N) Qbar)')
for a,b in [('originalJZeroArithmeticAction','gammaOnePicardArithmeticAction'),('originalJZero_isOpen_stabilizer','gammaOnePicard_isOpen_stabilizer'),('original_picard_fieldOfDefinition','gammaOne_picard_fieldOfDefinition'),('original_place_fieldOfDefinition','gammaOne_place_fieldOfDefinition'),('originalJZero N','J N'),('modularFunctionFieldOver N Qbar','functionFieldOver (Gamma1 N) Qbar'),('originalArithmeticPicardRep N (L := Qbar)','gamma1ArithmeticPicardRep Qbar N'),('originalArithmeticPlaceEquiv N','arithmeticPlaceEquiv (Gamma1 N)'),('originalArithmeticDivisorEquiv N','arithmeticDivisorEquiv (Gamma1 N)'),('originalArithmeticPlace N','arithmeticPlace (Gamma1 N)'),('originalArithmeticPicard_mk','arithmeticPicard_mk'),('originalArithmeticPicard N σ','arithmeticPicard (Gamma1 N) (by simp [Gamma1_mem, ModularGroup.T]) σ')]:s=s.replace(a,b)
t=p/'SourceGammaOnePicardFieldDefinition1416a.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
s=(p/'build_gamma_one_function_definition_1413.ps1').read_text(encoding='utf-8').replace('SourceGammaOneFunctionFieldDefinition1413a','SourceGammaOnePicardFieldDefinition1416a')
t=p/'build_gamma_one_picard_definition_1416.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
