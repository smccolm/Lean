from pathlib import Path
p=Path(__file__).parent
f=p/'SourceGammaOneHeckePrimeDegree.lean';s=f.read_text(encoding='utf-8')
a=p/'gamma-one-hecke-prime-degree-1296b';a.mkdir(exist_ok=False)
(a/(f.name+'.txt')).write_text(s,encoding='utf-8')
old='letI := SourceCurve.algebraAlong (heckeAlpha L M p)\n'
assert s.count(old)==2
def repl(m):
 indent=m.group(1)
 return indent+old+indent+'''letI : Module (laurentBaseChange L (x1FunctionField M))
'''+indent+'''    (laurentBaseChange L (x1x0FunctionFieldC ℚ M (p * M))) := Algebra.toModule
'''
import re
s=re.sub(r'(?m)^(\s*)'+re.escape(old),repl,s)
f.write_text(s,encoding='utf-8')
t=p/'compile_gamma_one_hecke_prime_degree_1296c.ps1';assert not t.exists()
t.write_text((p/'compile_gamma_one_hecke_prime_degree_1296b.ps1').read_text(encoding='utf-8').replace('1296b','1296c'),encoding='utf-8')
