from pathlib import Path
s=Path(r'E:\Lean\.tmp\dubon83')
p=s/'SourceReductionCoordinateAutomorphism1350a.lean'
t=p.read_text(encoding='utf-8').replace("map_mul' := rfl", "map_mul' := fun _ _ => rfl").replace("map_add' := rfl", "map_add' := fun _ _ => rfl")
(s/'SourceReductionCoordinateAutomorphism1350b.lean').write_text(t,encoding='utf-8')
p.rename(p.with_suffix('.lean.txt'))
