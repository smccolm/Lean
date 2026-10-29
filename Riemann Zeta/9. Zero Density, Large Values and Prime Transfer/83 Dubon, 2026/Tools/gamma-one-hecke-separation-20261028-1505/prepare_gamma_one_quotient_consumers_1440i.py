from pathlib import Path
s=Path(__file__).parent
f=s/'SourceGammaOneDiamondQuotientPolynomial1439h.lean';c=f.read_text(encoding='utf-8')
c=c.replace('[AddCommGroup W] [Module R W] [AddCommGroup Z] [Module R Z]','[AddCommMonoid W] [Module R W] [AddCommMonoid Z] [Module R Z]')
t=s/'SourceGammaOneDiamondQuotientPolynomial1439i.lean';assert not t.exists();t.write_text(c,encoding='utf-8')
t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
f=s/'SourceGammaOneDiamondQuotientHecke1440h.lean';c=f.read_text(encoding='utf-8').replace('SourceGammaOneDiamondQuotientPolynomial1439h','SourceGammaOneDiamondQuotientPolynomial1439i')
t=s/'SourceGammaOneDiamondQuotientHecke1440i.lean';assert not t.exists();t.write_text(c,encoding='utf-8')
t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
runner=(s/'build_gamma_one_quotient_consumers_1440h.ps1').read_text(encoding='utf-8').replace('1439h','1439i').replace('1440h','1440i')
t=s/'build_gamma_one_quotient_consumers_1440i.ps1';assert not t.exists();t.write_text(runner,encoding='utf-8')
print('Use only additive monoids in the linear projection lemma; no negative operation or stronger structure is needed.')
