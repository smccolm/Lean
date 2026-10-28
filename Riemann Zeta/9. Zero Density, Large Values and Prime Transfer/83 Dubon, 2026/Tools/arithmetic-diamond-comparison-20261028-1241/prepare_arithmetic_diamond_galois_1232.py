from pathlib import Path
p=Path(__file__).parent
src=(p/'SourceGammaOneDiamondComplexArithmetic.lean').read_text(encoding='utf-8')
start=src.index('namespace ')
s=src[start:]
s=s.replace('namespace Dubon2026.SourceFunctionField.GammaOne\n',
            'namespace Dubon2026.SourceFunctionField.GammaOne.ConstantField\n')
s=s.replace('end Dubon2026.SourceFunctionField.GammaOne\n',
            'end Dubon2026.SourceFunctionField.GammaOne.ConstantField\n')
s=s.replace('open CongruenceSubgroup\n','open CongruenceSubgroup\nlocal notation "Qbar" => AlgebraicClosure ℚ\n')
s=s.replace('ℂ','Qbar').replace('FC','FQ')
s=s.replace('diamondFieldHom','arithmeticDiamondHom')
s=s.replace('arithmeticRingAut_diamond_generator','arithmeticDiamond_generator_fixed')
s='''import SourceGammaOneArithmeticDiamondGenerators

/-! DUB-17/18 -> original all-weight association -> arithmetic Gamma1
diamond Galois compatibility. The proved fixed-generator identities and
literal field-generation induction establish commutation of the actual
arithmetic diamond with every original Qbar coefficient automorphism.
No rationality, Galois-equivariance or complex-extension premise remains.
The induced place, Picard and Tate consumers remain to be assembled.
-/
'''+s
f=p/'SourceGammaOneArithmeticDiamondGalois.lean'
assert not f.exists()
f.write_text(s,encoding='utf-8')
runner=(p/'compile_diamond_analytic_germs_1213a.ps1').read_text(encoding='utf-8')
runner=runner.replace('SourceGammaOneDiamondAnalyticGerms','SourceGammaOneArithmeticDiamondGalois').replace('1213a','1232a')
f=p/'compile_arithmetic_diamond_galois_1232a.ps1'
assert not f.exists()
f.write_text(runner,encoding='utf-8')
runner=(p/'compile_diamond_complex_arithmetic_1230a.ps1').read_text(encoding='utf-8').replace('1230a','1230b')
f=p/'compile_diamond_complex_arithmetic_1230b.ps1'
assert not f.exists()
f.write_text(runner,encoding='utf-8')
print('Prepared arithmetic field Galois consumer and fresh complex recheck after generator API extraction.')
