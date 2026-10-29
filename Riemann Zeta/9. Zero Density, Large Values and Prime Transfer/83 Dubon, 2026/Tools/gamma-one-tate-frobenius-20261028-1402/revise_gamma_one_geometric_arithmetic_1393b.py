from pathlib import Path
p=Path(__file__).parent
f=p/'SourceGammaOneGeometricArithmeticFrobenius1393a.lean';s=f.read_text(encoding='utf-8').replace('1392b','1392d')
s=s.replace('''  obtain ⟨g, hg, hquad⟩ :=
    exists_gammaOne_tate_frobenius_relation_of_degree_genus_eq A M ell.val hcop hdeg hgen d hd p hp''','''  have hs := exists_gammaOne_tate_frobenius_relation_of_degree_genus_eq A M ell.val
  have h1 := hs hcop
  have h2 := h1 hdeg
  have h3 := h2 hgen
  have h4 := h3 d hd p hp
  obtain ⟨g, hg, hquad⟩ := h4''')
t=p/'SourceGammaOneGeometricArithmeticFrobenius1393b.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
s=(p/'build_gamma_one_geometric_arithmetic_1393.ps1').read_text(encoding='utf-8').replace('1393a','1393b')
t=p/'build_gamma_one_geometric_arithmetic_1393b.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
