from pathlib import Path
p=Path(__file__).parent
f=p/'SourceGammaOneHeckePrimeDegree.lean';s=f.read_text(encoding='utf-8')
a=p/'gamma-one-hecke-prime-degree-1296c';a.mkdir(exist_ok=False)
(a/(f.name+'.txt')).write_text(s,encoding='utf-8')
old='  have h := gammaOne_over_prime_relfinrank L M p hcop\n'
new=old+'''  change relfinrank (laurentBaseChange L (x1FunctionField M))
    (laurentBaseChange L (x1x0FunctionFieldC ℚ M (p * M))) = p + 1 at h
'''
assert s.count(old)==1;f.write_text(s.replace(old,new),encoding='utf-8')
t=p/'compile_gamma_one_hecke_prime_degree_1296d.ps1';assert not t.exists()
t.write_text((p/'compile_gamma_one_hecke_prime_degree_1296c.ps1').read_text(encoding='utf-8').replace('1296c','1296d'),encoding='utf-8')
