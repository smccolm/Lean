from pathlib import Path
s=Path(__file__).parent
a=s/'SourceSiegelProductLeadingCoefficient1599a.lean';b=s/'SourceSiegelProductLeadingCoefficient1599b.lean';assert not b.exists()
c=a.read_text(encoding='utf-8').replace('simp only [series_zero, if_pos rfl, exponent]','simp [series_zero, exponent]')
b.write_text(c,encoding='utf-8');a.rename(a.with_suffix('.lean.txt'))
