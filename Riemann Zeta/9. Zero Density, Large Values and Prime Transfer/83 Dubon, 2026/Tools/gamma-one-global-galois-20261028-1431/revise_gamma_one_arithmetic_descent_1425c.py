from pathlib import Path
p=Path(__file__).parent
f=p/'SourceGammaOneTwistedArithmeticDescent1425b.lean'
assert f.with_suffix('.exit').read_text().strip()=='1'
s=f.read_text(encoding='utf-8')
old='(η (sourceAbsoluteArithmeticRestriction ((Q * p : ℕ) : 𝓞 ℚ) σ) : B)'
assert old in s
s=s.replace(old,'(η (sourceAbsoluteArithmeticRestriction ((Q * p : ℕ) : 𝓞 ℚ) σ)).val')
t=p/'SourceGammaOneTwistedArithmeticDescent1425c.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
inert=f.with_suffix('.lean.txt');assert not inert.exists();f.rename(inert)
s=(p/'build_gamma_one_arithmetic_descent_1425b.ps1').read_text(encoding='utf-8').replace('1425b','1425c')
t=p/'build_gamma_one_arithmetic_descent_1425c.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
