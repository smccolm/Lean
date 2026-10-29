from pathlib import Path
s=Path(__file__).parent
f=s/'SourceGammaOneDiamondQuotientLocal1449a.lean';c=f.read_text(encoding='utf-8').replace('let d : A.decompositionSubgroup ℚ','let d : ValuationSubring.decompositionSubgroup A ℚ')
t=s/'SourceGammaOneDiamondQuotientLocal1449b.lean';assert not t.exists();t.write_text(c,encoding='utf-8')
t=f.with_suffix('.lean.txt');assert not t.exists();f.rename(t)
print('Use the explicit valuation-subring API for the local notation.')
