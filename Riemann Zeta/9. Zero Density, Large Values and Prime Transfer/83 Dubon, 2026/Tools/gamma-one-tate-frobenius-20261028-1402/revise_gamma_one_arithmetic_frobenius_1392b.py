from pathlib import Path
p=Path(__file__).parent
f=p/'SourceGammaOneArithmeticFrobenius1392a.lean';s=f.read_text(encoding='utf-8')
s=s.replace('  apply sourceTateDual_arithmetic_quadratic','  exact sourceTateDual_arithmetic_quadratic')
a=s.index('  · rw [← map_mul');b=s.index('\nend\n',a)
s=s[:a]+'''    (by rw [← map_mul, mul_inv_cancel, map_one])
    (arithmeticTateGaloisRep_diamond M p g σ⁻¹)
    (sourceGammaOneHeckeDiamondCoefficient_square Q N w g ell.val hlabel) φ hfixed
'''+s[b:]
t=p/'SourceGammaOneArithmeticFrobenius1392b.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
s=(p/'build_gamma_one_picard_descent_1381f.ps1').read_text(encoding='utf-8').replace('SourceGammaOneHeckePicardDescent1381f','SourceGammaOneArithmeticFrobenius1392b')
t=p/'build_gamma_one_arithmetic_frobenius_1392b.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
