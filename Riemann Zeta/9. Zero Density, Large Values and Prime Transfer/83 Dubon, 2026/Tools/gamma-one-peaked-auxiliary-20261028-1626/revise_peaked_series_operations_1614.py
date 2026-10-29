from pathlib import Path
s=Path(__file__).parent
for a,b in [('SourcePeakedSeriesOperations1611a','SourcePeakedSeriesOperations1611b'),('SourcePeakedShiftedSeries1613a','SourcePeakedShiftedSeries1613b')]:
 f=s/(a+'.lean');g=s/(b+'.lean');assert not g.exists()
 c=f.read_text(encoding='utf-8').replace('* I *','* Complex.I *').replace('import SourcePeakedSeriesOperations1611a','import SourcePeakedSeriesOperations1611b')
 g.write_text(c,encoding='utf-8');f.rename(f.with_suffix('.lean.txt'))
