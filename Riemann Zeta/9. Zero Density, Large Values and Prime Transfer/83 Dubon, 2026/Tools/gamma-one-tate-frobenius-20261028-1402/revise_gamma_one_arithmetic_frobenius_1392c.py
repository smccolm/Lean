from pathlib import Path
p=Path(__file__).parent
f=p/'SourceGammaOneArithmeticFrobenius1392b.lean';s=f.read_text(encoding='utf-8')
s=s.replace('  exact sourceTateDual_arithmetic_quadratic','  have h := sourceTateDual_arithmetic_quadratic')
s=s.replace(' φ hfixed\n',' φ hfixed\n  exact h\n')
t=p/'SourceGammaOneArithmeticFrobenius1392c.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
s=(p/'build_gamma_one_arithmetic_frobenius_1392b.ps1').read_text(encoding='utf-8').replace('1392b','1392c')
t=p/'build_gamma_one_arithmetic_frobenius_1392c.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
