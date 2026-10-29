from pathlib import Path
s=Path(__file__).parent
f=s/'SourceGammaOneDiamondQuotientGalois1438g.lean';c=f.read_text(encoding='utf-8')
a=c.index('private local instance : HasQuotient');b=c.index('/-- The actual Galois action',a)
c=c[:a]+c[b:]
t=s/'SourceGammaOneDiamondQuotientGalois1438h.lean';assert not t.exists();t.write_text(c,encoding='utf-8')
t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
print('Use native quotient inference with cached carrier structures; remove redundant instance construction.')
