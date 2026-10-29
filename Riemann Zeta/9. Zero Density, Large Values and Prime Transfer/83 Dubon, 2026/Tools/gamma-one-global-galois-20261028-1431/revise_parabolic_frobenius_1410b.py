from pathlib import Path
p=Path(__file__).parent
old=p/'SourceGammaOneParabolicGaloisFrobenius1410a.lean'
assert old.with_suffix('.exit').read_text().strip()=='1'
code=old.read_text(encoding='utf-8')
code=code.replace('  obtain ⟨φ, hφ, hfixed⟩ := exists_binaryTate_restriction_diamond_fixed Q p n w hlarge x', '  have hl := exists_binaryTate_restriction_diamond_fixed Q p n w\n  have hl1 := hl hlarge\n  have hl2 := hl1 x\n  obtain ⟨φ, hφ, hfixed⟩ := hl2')
target=p/'SourceGammaOneParabolicGaloisFrobenius1410b.lean';assert not target.exists();target.write_text(code,encoding='utf-8')
inert=old.with_suffix('.lean.txt');assert not inert.exists();old.rename(inert)
s=(p/'build_gamma_one_parabolic_frobenius_1410.ps1').read_text(encoding='utf-8').replace('1410a','1410b')
t=p/'build_gamma_one_parabolic_frobenius_1410b.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
