from pathlib import Path
s=Path(r'E:\Lean\.tmp\dubon83')
p=s/'SourceGammaOneHeckeFractionProduct1353a.lean'
(s/'SourceGammaOneHeckeFractionProduct1353b.lean').write_text(p.read_text(encoding='utf-8').replace('  rw [coeffMap_qTwist_commRing, map_pow, hunit]\n  rfl','  rw [coeffMap_qTwist_commRing, map_pow, hunit]'),encoding='utf-8')
p.rename(p.with_suffix('.lean.txt'))
