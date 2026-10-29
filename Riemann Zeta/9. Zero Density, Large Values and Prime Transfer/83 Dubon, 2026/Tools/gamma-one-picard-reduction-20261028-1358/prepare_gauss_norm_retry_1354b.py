from pathlib import Path
s=Path(r'E:\Lean\.tmp\dubon83')
p=s/'SourceGammaOneHeckeGaussNorm1354a.lean'
(s/'SourceGammaOneHeckeGaussNorm1354b.lean').write_text(p.read_text(encoding='utf-8').replace('local notation "FF" => functionFieldOver Γ Qbar','local notation "FF" => laurentBaseChange Qbar (x1FunctionField M)'),encoding='utf-8')
p.rename(p.with_suffix('.lean.txt'))
