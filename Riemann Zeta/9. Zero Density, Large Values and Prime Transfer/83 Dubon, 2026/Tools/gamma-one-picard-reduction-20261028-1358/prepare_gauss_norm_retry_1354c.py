from pathlib import Path
s=Path(r'E:\Lean\.tmp\dubon83')
p=s/'SourceGammaOneHeckeGaussNorm1354b.lean'
(s/'SourceGammaOneHeckeGaussNorm1354c.lean').write_text(p.read_text(encoding='utf-8').replace('Module.finrank Qbar⟮jCoordinateOver Γ Qbar⟯ FF =','Module.finrank Qbar⟮jCoordinateOver Γ Qbar⟯ (functionFieldOver Γ Qbar) ='),encoding='utf-8')
p.rename(p.with_suffix('.lean.txt'))
