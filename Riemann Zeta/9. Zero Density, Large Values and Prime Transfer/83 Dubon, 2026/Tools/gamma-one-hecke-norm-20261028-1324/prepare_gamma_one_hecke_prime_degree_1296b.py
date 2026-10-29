from pathlib import Path
p=Path(__file__).parent
f=p/'SourceGammaOneHeckePrimeDegree.lean';s=f.read_text(encoding='utf-8')
a=p/'gamma-one-hecke-prime-degree-1296a';a.mkdir(exist_ok=False)
(a/(f.name+'.txt')).write_text(s,encoding='utf-8')
s=s.replace('Subgroup.index_ne_zero (H :=','Subgroup.FiniteIndex.index_ne_zero (H :=')
old='''Module.finrank (functionFieldOver (Gamma1 M) L)
      (functionFieldOver (Gamma1 M ⊓ Gamma0 (p * M)) L) = p + 1 := by'''
new='''Module.finrank (laurentBaseChange L (x1FunctionField M))
      (laurentBaseChange L (x1x0FunctionFieldC ℚ M (p * M))) = p + 1 := by'''
assert s.count(old)==1;s=s.replace(old,new)
f.write_text(s,encoding='utf-8')
t=p/'compile_gamma_one_hecke_prime_degree_1296b.ps1';assert not t.exists()
t.write_text((p/'compile_gamma_one_hecke_prime_degree_1296a.ps1').read_text(encoding='utf-8').replace('1296a','1296b'),encoding='utf-8')
