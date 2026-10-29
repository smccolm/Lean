from pathlib import Path
s=Path(r'E:\Lean\.tmp\dubon83')
p=s/'SourceGammaOneKummerPowerLifting1344b.lean'
(s/'SourceGammaOneKummerPowerLifting1344c.lean').write_text(p.read_text(encoding='utf-8').replace('IsScalarTower.of_algebraMap_eq fun _ => rfl','IsScalarTower.of_algebraMap_eq (R := Qbar) (S := FF) (A := E) fun _ => rfl'),encoding='utf-8')
p.rename(p.with_suffix('.lean.txt'))
