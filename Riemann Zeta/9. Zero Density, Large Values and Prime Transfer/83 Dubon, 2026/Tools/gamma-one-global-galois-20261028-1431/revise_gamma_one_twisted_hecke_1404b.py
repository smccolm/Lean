from pathlib import Path
p=Path(__file__).parent
f=p/'SourceCyclotomicHomogeneousHecke1403a.lean';s=f.read_text(encoding='utf-8')
s=s.replace('  rw [smul_mul_assoc, mul_smul_comm, hpoly.eq]','  rw [smul_mul_assoc, mul_smul_comm]\n  exact congrArg ((u : R) • ·) hpoly.eq')
t=p/'SourceCyclotomicHomogeneousHecke1403b.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
f=p/'SourceGammaOneTwistedGaloisHecke1404a.lean';s=f.read_text(encoding='utf-8').replace('1401d','1401e').replace('1403a','1403b')
t=p/'SourceGammaOneTwistedGaloisHecke1404b.lean';assert not t.exists();t.write_text(s,encoding='utf-8')
t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
s=(p/'build_gamma_one_twisted_hecke_1404.ps1').read_text(encoding='utf-8').replace('1403a','1403b').replace('1404a','1404b')
t=p/'build_gamma_one_twisted_hecke_1404b.ps1';assert not t.exists();t.write_text(s,encoding='utf-8')
