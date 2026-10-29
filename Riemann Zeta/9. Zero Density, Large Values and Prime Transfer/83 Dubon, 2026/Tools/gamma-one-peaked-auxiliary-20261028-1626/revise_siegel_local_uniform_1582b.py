from pathlib import Path
s=Path(__file__).parent
f=s/'SourceSiegelProductLocalUniform1582a.lean'
t=f.read_text(encoding='utf-8').replace('have h := hasProdUniformlyOn_nat_one_add hcK hs','have h := Summable.hasProdUniformlyOn_nat_one_add hcK hs')
assert not f.with_suffix('.lean.txt').exists();f.rename(f.with_suffix('.lean.txt'))
n=s/'SourceSiegelProductLocalUniform1582b.lean';assert not n.exists();n.write_text(t,encoding='utf-8')
f=s/'SourceSiegelProductTaylorExpansion1583a.lean'
t=f.read_text(encoding='utf-8').replace('import SourceSiegelProductLocalUniform1582a','import SourceSiegelProductLocalUniform1582b')
assert not f.with_suffix('.lean.txt').exists();f.rename(f.with_suffix('.lean.txt'))
n=s/'SourceSiegelProductTaylorExpansion1583b.lean';assert not n.exists();n.write_text(t,encoding='utf-8')
