from pathlib import Path
p=Path(__file__).parent
f=p/'SourceGammaOneFiniteTateDual1418b.lean';assert f.with_suffix('.exit').read_text().strip()=='0'
assert 'warning:' in f.with_suffix('.log').read_text(encoding='utf-16')
s=f.read_text(encoding='utf-8').replace('theorem binaryArithmeticTateDual_eq_of_proj_eq','omit [NeZero Q] in\ntheorem binaryArithmeticTateDual_eq_of_proj_eq').replace('simp only [map_pow, map_natCast,','simp only [map_natCast,')
t=p/'SourceGammaOneFiniteTateDual1418c.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
inert=f.with_suffix('.lean.txt');assert not inert.exists();f.rename(inert)
s=(p/'build_gamma_one_finite_tate_dual_1418b.ps1').read_text(encoding='utf-8').replace('1418b','1418c')
t=p/'build_gamma_one_finite_tate_dual_1418c.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
f=p/'SourceGammaOneTwistedCongruence1419a.lean';assert not f.with_suffix('.log').exists()
f.write_text(f.read_text(encoding='utf-8').replace('SourceGammaOneFiniteTateDual1418b','SourceGammaOneFiniteTateDual1418c'),encoding='utf-8')
