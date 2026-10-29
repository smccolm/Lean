from pathlib import Path
p=Path(__file__).parent
f=p/'SourceGammaOneArithmeticFrobenius1392c.lean';s=f.read_text(encoding='utf-8')
s=s.replace('(by rw [← map_mul, mul_inv_cancel, map_one])','''(((arithmeticTateGaloisRep M p).map_mul σ σ⁻¹).symm.trans
      ((congrArg (arithmeticTateGaloisRep M p) (mul_inv_cancel σ)).trans
        (arithmeticTateGaloisRep M p).map_one))''')
t=p/'SourceGammaOneArithmeticFrobenius1392d.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
s=(p/'build_gamma_one_arithmetic_frobenius_1392c.ps1').read_text(encoding='utf-8').replace('1392c','1392d')
t=p/'build_gamma_one_arithmetic_frobenius_1392d.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
