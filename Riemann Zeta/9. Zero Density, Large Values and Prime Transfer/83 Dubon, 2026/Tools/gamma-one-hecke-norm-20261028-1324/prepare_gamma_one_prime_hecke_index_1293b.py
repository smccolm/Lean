from pathlib import Path
p=Path(__file__).parent
f=p/'SourceGammaOnePrimeHeckeIndex.lean'
s=f.read_text(encoding='utf-8')
a=p/'gamma-one-prime-hecke-index-1293a';a.mkdir(exist_ok=False)
(a/(f.name+'.txt')).write_text(s,encoding='utf-8')
old='private theorem borel_index_eq_gamma0 (n : ℕ) :'
assert s.count(old)==1
f.write_text(s.replace(old,'private theorem borel_index_eq_gamma0 (n : ℕ) [NeZero n] :'),encoding='utf-8')
t=p/'compile_gamma_one_prime_hecke_index_1293b.ps1';assert not t.exists()
t.write_text((p/'compile_gamma_one_prime_hecke_index_1293a.ps1').read_text(encoding='utf-8').replace('1293a','1293b'),encoding='utf-8')
