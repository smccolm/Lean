from pathlib import Path
s=Path(r'E:\Lean\.tmp\dubon83')
p=s/'SourceJointSeparablePoleDimension1342a.lean'
(s/'SourceJointSeparablePoleDimension1342b.lean').write_text(p.read_text(encoding='utf-8').replace('import Dubon2026.SourceJointReductionPoleCharts','import Dubon2026.SourceJointReductionPoleCharts\nimport Dubon2026.SourceResidueClosedValuationField'),encoding='utf-8')
p.rename(p.with_suffix('.lean.txt'))
