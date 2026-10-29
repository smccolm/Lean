from pathlib import Path
s=Path(__file__).parent
a=s/'SourceSiegelFiniteProductExpansion1601a.lean';b=s/'SourceSiegelFiniteProductExpansion1601b.lean';assert not b.exists()
c=a.read_text(encoding='utf-8').replace('simpa only [qParam_pow_eq, orderSum]','simpa [qParam_pow_eq, orderSum]').replace('  · exact tendsto_productSeries N e','  · simpa [orderSum] using tendsto_productSeries N e')
b.write_text(c,encoding='utf-8');a.rename(a.with_suffix('.lean.txt'))
