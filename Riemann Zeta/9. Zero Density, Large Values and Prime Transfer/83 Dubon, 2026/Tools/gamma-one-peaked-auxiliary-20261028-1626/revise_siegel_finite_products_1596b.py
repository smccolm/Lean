from pathlib import Path
s=Path(__file__).parent
old=s/'SourceSiegelFiniteSeriesProducts1596a.lean';new=s/'SourceSiegelFiniteSeriesProducts1596b.lean'
assert not new.exists()
c=old.read_text(encoding='utf-8')
a='  induction s using Finset.induction_on with\n';i=c.index(a,c.index('theorem coeff_prod_mem'))
c=c[:i]+c[i:].replace(a,'  induction s using Finset.induction_on generalizing n with\n',1)
new.write_text(c,encoding='utf-8');old.rename(old.with_suffix('.lean.txt'))
print('Generalized coefficient index in finite-product induction; failed proof retained inert.')
