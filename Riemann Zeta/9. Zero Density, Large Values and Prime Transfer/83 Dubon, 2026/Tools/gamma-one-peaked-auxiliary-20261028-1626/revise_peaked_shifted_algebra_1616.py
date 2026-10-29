from pathlib import Path
s=Path(__file__).parent
a=s/'SourcePeakedShiftedCoefficients1615a.lean';b=s/'SourcePeakedShiftedCoefficients1615b.lean';assert not b.exists()
b.write_text(a.read_text(encoding='utf-8').replace('convert h using 1 <;> ring','convert h using 1; ring'),encoding='utf-8');a.rename(a.with_suffix('.lean.txt'))
a=s/'SourcePeakedShiftedSeries1613b.lean';b=s/'SourcePeakedShiftedSeries1613c.lean';assert not b.exists()
c=a.read_text(encoding='utf-8').replace('import SourcePeakedSeriesOperations1611b','import SourcePeakedSeriesOperations1611b\nimport SourcePeakedShiftedCoefficients1615b')
i=c.index('  have hC0 :');j=c.index('  set q :=',i)
c=c[:i]+'  have hC0 := phase_ne_zero N m\n'+c[j:]
b.write_text(c,encoding='utf-8');a.rename(a.with_suffix('.lean.txt'))
